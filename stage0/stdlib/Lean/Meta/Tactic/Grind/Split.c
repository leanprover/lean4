// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Split
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.SearchM import Lean.Meta.Tactic.Grind.Intro import Lean.Meta.Tactic.Grind.Cases import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Internalize
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
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16;
static lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7;
lean_object* l_Lean_Environment_header(lean_object*);
static lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_source(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__3;
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__17;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqSplitStatus_beq(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8;
lean_object* l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9;
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSplitStatus;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSplitStatus_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_casesMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6;
static lean_object* l_Lean_Meta_Grind_splitNext___lam__9___closed__1;
uint8_t l_Lean_Meta_Grind_Goal_isCongruent(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0;
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3;
static lean_object* l_Lean_Meta_Grind_instBEqSplitStatus___closed__0;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus___closed__0;
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___boxed(lean_object**);
uint8_t l_Lean_isPrivateName(lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__19;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_SplitStatus_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec_ref(x_1);
x_6 = lean_box(x_4);
x_7 = lean_box(x_5);
x_8 = lean_apply_3(x_2, x_3, x_6, x_7);
return x_8;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_SplitStatus_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_resolved_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_notReady_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitStatus_ready_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_SplitStatus_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqSplitStatus_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_15 = lean_nat_dec_eq(x_7, x_10);
if (x_15 == 0)
{
return x_15;
}
else
{
if (x_8 == 0)
{
if (x_11 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
return x_8;
}
}
else
{
x_13 = x_11;
goto block_14;
}
}
block_14:
{
if (x_13 == 0)
{
return x_13;
}
else
{
if (x_9 == 0)
{
if (x_12 == 0)
{
return x_13;
}
else
{
return x_9;
}
}
else
{
return x_12;
}
}
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_instBEqSplitStatus_beq(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed), 2, 0);
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
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.SplitStatus.notReady", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.SplitStatus.resolved", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.SplitStatus.ready", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1024u);
x_18 = lean_nat_dec_le(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4;
x_10 = x_19;
goto block_16;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5;
x_10 = x_20;
goto block_16;
}
}
case 1:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4;
x_3 = x_23;
goto block_9;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5;
x_3 = x_24;
goto block_9;
}
}
default: 
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_45; uint8_t x_46; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec_ref(x_1);
x_45 = lean_unsigned_to_nat(1024u);
x_46 = lean_nat_dec_le(x_45, x_2);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4;
x_28 = x_47;
goto block_44;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5;
x_28 = x_48;
goto block_44;
}
block_44:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_box(1);
x_30 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8;
x_31 = l_Nat_reprFast(x_25);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = l_Bool_repr___redArg(x_26);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
x_38 = l_Bool_repr___redArg(x_27);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
x_41 = 0;
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = l_Repr_addAppParen(x_42, x_2);
return x_43;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_instReprSplitStatus_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed), 2, 0);
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_33);
x_37 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_3, x_4, x_5, x_36);
x_7 = x_37;
goto block_32;
}
else
{
lean_dec_ref(x_1);
x_7 = x_33;
goto block_32;
}
}
else
{
lean_dec_ref(x_1);
x_7 = x_33;
goto block_32;
}
block_32:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_8);
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
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_35; 
lean_inc_ref(x_1);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec_ref(x_35);
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
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_dec_ref(x_35);
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
lean_dec_ref(x_59);
x_63 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_5, x_6, x_7, x_62);
x_9 = x_63;
goto block_34;
}
else
{
lean_dec_ref(x_3);
x_9 = x_59;
goto block_34;
}
}
else
{
lean_dec_ref(x_3);
x_9 = x_59;
goto block_34;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_10);
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
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_35; 
lean_inc_ref(x_1);
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
lean_dec_ref(x_35);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_39);
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
lean_dec_ref(x_49);
x_53 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_5, x_6, x_7, x_52);
x_9 = x_53;
goto block_34;
}
else
{
lean_dec_ref(x_3);
x_9 = x_49;
goto block_34;
}
}
else
{
lean_dec_ref(x_3);
x_9 = x_49;
goto block_34;
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_10);
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
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_34; lean_object* x_49; lean_object* x_53; lean_object* x_74; lean_object* x_89; 
lean_inc_ref(x_1);
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
lean_dec_ref(x_89);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_93);
lean_inc_ref(x_2);
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
lean_dec_ref(x_103);
lean_inc_ref(x_3);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
x_112 = lean_ctor_get(x_89, 1);
lean_inc(x_112);
lean_dec_ref(x_89);
lean_inc_ref(x_2);
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
lean_dec_ref(x_113);
lean_inc_ref(x_3);
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
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_inc(x_14);
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
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec_ref(x_13);
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
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec_ref(x_34);
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
lean_dec_ref(x_3);
x_13 = x_38;
goto block_33;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec_ref(x_38);
x_42 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_5, x_6, x_7, x_41);
x_13 = x_42;
goto block_33;
}
}
else
{
lean_dec_ref(x_3);
x_13 = x_38;
goto block_33;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec_ref(x_34);
x_9 = x_43;
goto block_12;
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
x_55 = lean_unbox(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_inc(x_54);
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
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_dec_ref(x_53);
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
x_76 = lean_unbox(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec_ref(x_74);
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
lean_dec_ref(x_3);
x_53 = x_78;
goto block_73;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec_ref(x_78);
x_82 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_5, x_6, x_7, x_81);
x_53 = x_82;
goto block_73;
}
}
else
{
lean_dec_ref(x_3);
x_53 = x_78;
goto block_73;
}
}
else
{
lean_object* x_83; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec_ref(x_74);
x_49 = x_83;
goto block_52;
}
}
else
{
uint8_t x_84; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_dec_ref(x_26);
lean_inc_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
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
lean_dec_ref(x_26);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
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
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
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
lean_dec_ref(x_21);
x_15 = x_22;
x_16 = x_23;
goto block_20;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget_borrowed(x_2, x_4);
x_19 = lean_array_fget_borrowed(x_3, x_4);
lean_inc_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_18);
x_20 = lean_apply_12(x_1, x_5, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
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
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
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
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(x_1, x_13, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_26 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(x_1, x_23, x_24, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_st_ref_get(x_2, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 14);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_18);
lean_dec_ref(x_16);
x_19 = lean_box(x_11);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 14, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_20, x_18, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec_ref(x_18);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___boxed(lean_object** _args) {
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
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
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
x_19 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_3);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_unknownIdentifierMessageTag;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0;
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
x_4 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
x_3 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("A private declaration `", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` (from the current module) exists but would need to be public to access here.", 78, 78);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("A public declaration `", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` exists but is imported privately; consider adding `public import ", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`.", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` (from `", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`) exists but would need to be public to access here.", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_24 = l_Lean_Name_isAnonymous(x_2);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_16, sizeof(void*)*8);
if (x_25 == 0)
{
lean_dec_ref(x_16);
lean_free_object(x_12);
lean_dec(x_2);
goto block_23;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_inc_ref(x_16);
x_26 = l_Lean_Environment_setExporting(x_16, x_24);
lean_inc(x_2);
lean_inc_ref(x_26);
x_27 = l_Lean_Environment_contains(x_26, x_2, x_25);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_16);
lean_free_object(x_12);
lean_dec(x_2);
goto block_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
x_29 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6;
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
lean_inc(x_2);
x_32 = l_Lean_MessageData_ofConstName(x_2, x_24);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_32);
lean_ctor_set(x_12, 0, x_31);
x_33 = l_Lean_Environment_getModuleIdxFor_x3f(x_16, x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_16);
lean_dec(x_2);
x_34 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
x_36 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_note(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
x_17 = x_39;
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec_ref(x_33);
x_41 = lean_box(0);
x_42 = l_Lean_Environment_header(x_16);
lean_dec_ref(x_16);
x_43 = l_Lean_EnvironmentHeader_moduleNames(x_42);
x_44 = lean_array_get(x_41, x_43, x_40);
lean_dec(x_40);
lean_dec_ref(x_43);
x_45 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_12);
x_48 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofName(x_44);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_note(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_17 = x_55;
goto block_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_12);
x_58 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MessageData_ofName(x_44);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_note(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
x_17 = x_65;
goto block_20;
}
}
}
}
}
else
{
lean_dec_ref(x_16);
lean_free_object(x_12);
lean_dec(x_2);
goto block_23;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_19;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_22;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_76; 
x_66 = lean_ctor_get(x_12, 0);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_12);
x_68 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_68);
lean_dec(x_66);
x_76 = l_Lean_Name_isAnonymous(x_2);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_68, sizeof(void*)*8);
if (x_77 == 0)
{
lean_dec_ref(x_68);
lean_dec(x_2);
goto block_75;
}
else
{
lean_object* x_78; uint8_t x_79; 
lean_inc_ref(x_68);
x_78 = l_Lean_Environment_setExporting(x_68, x_76);
lean_inc(x_2);
lean_inc_ref(x_78);
x_79 = l_Lean_Environment_contains(x_78, x_2, x_77);
if (x_79 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_68);
lean_dec(x_2);
goto block_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
x_81 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6;
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
lean_inc(x_2);
x_84 = l_Lean_MessageData_ofConstName(x_2, x_76);
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Environment_getModuleIdxFor_x3f(x_68, x_2);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_68);
lean_dec(x_2);
x_87 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_MessageData_note(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
x_69 = x_92;
goto block_72;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec_ref(x_86);
x_94 = lean_box(0);
x_95 = l_Lean_Environment_header(x_68);
lean_dec_ref(x_68);
x_96 = l_Lean_EnvironmentHeader_moduleNames(x_95);
x_97 = lean_array_get(x_94, x_96, x_93);
lean_dec(x_93);
lean_dec_ref(x_96);
x_98 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_99 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_85);
x_101 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_MessageData_ofName(x_97);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MessageData_note(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_107);
x_69 = x_108;
goto block_72;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_85);
x_111 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_MessageData_ofName(x_97);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_MessageData_note(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_117);
x_69 = x_118;
goto block_72;
}
}
}
}
}
else
{
lean_dec_ref(x_68);
lean_dec(x_2);
goto block_75;
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_69, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
return x_71;
}
block_75:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_box(0);
x_74 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
lean_inc_ref(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
lean_inc_ref(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
lean_inc_ref(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(3, 2, 0);
} else {
 x_38 = x_33;
 lean_ctor_set_tag(x_38, 3);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_2, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
x_27 = lean_ctor_get(x_9, 11);
x_28 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_29 = lean_ctor_get(x_9, 12);
x_30 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_31 = lean_ctor_get(x_9, 13);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_32 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_33 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_19);
lean_ctor_set(x_33, 4, x_20);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_22);
lean_ctor_set(x_33, 7, x_23);
lean_ctor_set(x_33, 8, x_24);
lean_ctor_set(x_33, 9, x_25);
lean_ctor_set(x_33, 10, x_26);
lean_ctor_set(x_33, 11, x_27);
lean_ctor_set(x_33, 12, x_29);
lean_ctor_set(x_33, 13, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*14, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*14 + 1, x_30);
x_34 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_2, x_7, x_8, x_33, x_10, x_11);
lean_dec_ref(x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unknown constant `", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__1;
x_13 = 0;
lean_inc(x_2);
x_14 = l_Lean_MessageData_ofConstName(x_2, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = 0;
lean_inc(x_1);
x_17 = l_Lean_Environment_find_x3f(x_15, x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_free_object(x_11);
x_18 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_8);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = 0;
lean_inc(x_1);
x_24 = l_Lean_Environment_find_x3f(x_22, x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_8);
lean_dec(x_1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(x_1, x_8, x_10);
return x_11;
}
}
static double _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_st_ref_take(x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 4);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; double x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_24 = 0;
x_25 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_24);
x_27 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_8);
x_29 = l_Lean_PersistentArray_push___redArg(x_22, x_13);
lean_ctor_set(x_15, 0, x_29);
x_30 = lean_st_ref_set(x_6, x_14, x_17);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_box(0);
lean_ctor_set(x_9, 1, x_31);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
else
{
uint64_t x_33; lean_object* x_34; double x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get_uint64(x_15, sizeof(void*)*1);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_36 = 0;
x_37 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_38 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_float(x_38, sizeof(void*)*2, x_35);
lean_ctor_set_float(x_38, sizeof(void*)*2 + 8, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_36);
x_39 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_40 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_40);
lean_ctor_set(x_13, 0, x_8);
x_41 = l_Lean_PersistentArray_push___redArg(x_34, x_13);
x_42 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint64(x_42, sizeof(void*)*1, x_33);
lean_ctor_set(x_14, 4, x_42);
x_43 = lean_st_ref_set(x_6, x_14, x_17);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
lean_ctor_set(x_9, 1, x_44);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; double x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
x_48 = lean_ctor_get(x_14, 2);
x_49 = lean_ctor_get(x_14, 3);
x_50 = lean_ctor_get(x_14, 5);
x_51 = lean_ctor_get(x_14, 6);
x_52 = lean_ctor_get(x_14, 7);
x_53 = lean_ctor_get(x_14, 8);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_54 = lean_ctor_get_uint64(x_15, sizeof(void*)*1);
x_55 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_56 = x_15;
} else {
 lean_dec_ref(x_15);
 x_56 = lean_box(0);
}
x_57 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_58 = 0;
x_59 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_60 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_float(x_60, sizeof(void*)*2, x_57);
lean_ctor_set_float(x_60, sizeof(void*)*2 + 8, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 16, x_58);
x_61 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_62 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_11);
lean_ctor_set(x_62, 2, x_61);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_62);
lean_ctor_set(x_13, 0, x_8);
x_63 = l_Lean_PersistentArray_push___redArg(x_55, x_13);
if (lean_is_scalar(x_56)) {
 x_64 = lean_alloc_ctor(0, 1, 8);
} else {
 x_64 = x_56;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint64(x_64, sizeof(void*)*1, x_54);
x_65 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_65, 2, x_48);
lean_ctor_set(x_65, 3, x_49);
lean_ctor_set(x_65, 4, x_64);
lean_ctor_set(x_65, 5, x_50);
lean_ctor_set(x_65, 6, x_51);
lean_ctor_set(x_65, 7, x_52);
lean_ctor_set(x_65, 8, x_53);
x_66 = lean_st_ref_set(x_6, x_65, x_17);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_box(0);
lean_ctor_set(x_9, 1, x_67);
lean_ctor_set(x_9, 0, x_68);
return x_9;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; double x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_dec(x_13);
x_70 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_14, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_14, 5);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_14, 6);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_14, 7);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_14, 8);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 lean_ctor_release(x_14, 7);
 lean_ctor_release(x_14, 8);
 x_78 = x_14;
} else {
 lean_dec_ref(x_14);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get_uint64(x_15, sizeof(void*)*1);
x_80 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_80);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_81 = x_15;
} else {
 lean_dec_ref(x_15);
 x_81 = lean_box(0);
}
x_82 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_83 = 0;
x_84 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_85 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_float(x_85, sizeof(void*)*2, x_82);
lean_ctor_set_float(x_85, sizeof(void*)*2 + 8, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 16, x_83);
x_86 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_87 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_11);
lean_ctor_set(x_87, 2, x_86);
lean_inc(x_8);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_8);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_PersistentArray_push___redArg(x_80, x_88);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 1, 8);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_uint64(x_90, sizeof(void*)*1, x_79);
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 9, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_71);
lean_ctor_set(x_91, 2, x_72);
lean_ctor_set(x_91, 3, x_73);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set(x_91, 5, x_74);
lean_ctor_set(x_91, 6, x_75);
lean_ctor_set(x_91, 7, x_76);
lean_ctor_set(x_91, 8, x_77);
x_92 = lean_st_ref_set(x_6, x_91, x_69);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_box(0);
lean_ctor_set(x_9, 1, x_93);
lean_ctor_set(x_9, 0, x_94);
return x_9;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; lean_object* x_113; double x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_9);
x_97 = lean_st_ref_take(x_6, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 4);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 2);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_98, 3);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_98, 5);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_98, 6);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_98, 7);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_98, 8);
lean_inc_ref(x_109);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 lean_ctor_release(x_98, 4);
 lean_ctor_release(x_98, 5);
 lean_ctor_release(x_98, 6);
 lean_ctor_release(x_98, 7);
 lean_ctor_release(x_98, 8);
 x_110 = x_98;
} else {
 lean_dec_ref(x_98);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get_uint64(x_99, sizeof(void*)*1);
x_112 = lean_ctor_get(x_99, 0);
lean_inc_ref(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
 x_113 = lean_box(0);
}
x_114 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_115 = 0;
x_116 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_117 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_float(x_117, sizeof(void*)*2, x_114);
lean_ctor_set_float(x_117, sizeof(void*)*2 + 8, x_114);
lean_ctor_set_uint8(x_117, sizeof(void*)*2 + 16, x_115);
x_118 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_119 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_95);
lean_ctor_set(x_119, 2, x_118);
lean_inc(x_8);
if (lean_is_scalar(x_101)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_101;
}
lean_ctor_set(x_120, 0, x_8);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_PersistentArray_push___redArg(x_112, x_120);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 1, 8);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_uint64(x_122, sizeof(void*)*1, x_111);
if (lean_is_scalar(x_110)) {
 x_123 = lean_alloc_ctor(0, 9, 0);
} else {
 x_123 = x_110;
}
lean_ctor_set(x_123, 0, x_102);
lean_ctor_set(x_123, 1, x_103);
lean_ctor_set(x_123, 2, x_104);
lean_ctor_set(x_123, 3, x_105);
lean_ctor_set(x_123, 4, x_122);
lean_ctor_set(x_123, 5, x_106);
lean_ctor_set(x_123, 6, x_107);
lean_ctor_set(x_123, 7, x_108);
lean_ctor_set(x_123, 8, x_109);
x_124 = lean_st_ref_set(x_6, x_123, x_100);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
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
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split resolved: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Or", 2, 2);
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
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_277; 
lean_inc_ref(x_1);
x_277 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
if (lean_obj_tag(x_277) == 0)
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_292; uint8_t x_293; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = lean_ctor_get(x_277, 1);
x_292 = l_Lean_Expr_cleanupAnnotations(x_279);
x_293 = l_Lean_Expr_isApp(x_292);
if (x_293 == 0)
{
lean_dec_ref(x_292);
lean_free_object(x_277);
x_281 = x_2;
x_282 = x_3;
x_283 = x_4;
x_284 = x_5;
x_285 = x_6;
x_286 = x_7;
x_287 = x_8;
x_288 = x_9;
goto block_291;
}
else
{
lean_object* x_294; uint8_t x_295; 
lean_inc_ref(x_292);
x_294 = l_Lean_Expr_appFnCleanup___redArg(x_292);
x_295 = l_Lean_Expr_isApp(x_294);
if (x_295 == 0)
{
lean_dec_ref(x_294);
lean_dec_ref(x_292);
lean_free_object(x_277);
x_281 = x_2;
x_282 = x_3;
x_283 = x_4;
x_284 = x_5;
x_285 = x_6;
x_286 = x_7;
x_287 = x_8;
x_288 = x_9;
goto block_291;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_296 = lean_ctor_get(x_292, 1);
lean_inc_ref(x_296);
lean_dec_ref(x_292);
x_297 = lean_ctor_get(x_294, 1);
lean_inc_ref(x_297);
x_298 = l_Lean_Expr_appFnCleanup___redArg(x_294);
x_299 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_300 = l_Lean_Expr_isConstOf(x_298, x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
x_302 = l_Lean_Expr_isConstOf(x_298, x_301);
if (x_302 == 0)
{
uint8_t x_303; 
x_303 = l_Lean_Expr_isApp(x_298);
if (x_303 == 0)
{
lean_dec_ref(x_298);
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_free_object(x_277);
x_281 = x_2;
x_282 = x_3;
x_283 = x_4;
x_284 = x_5;
x_285 = x_6;
x_286 = x_7;
x_287 = x_8;
x_288 = x_9;
goto block_291;
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = l_Lean_Expr_appFnCleanup___redArg(x_298);
x_305 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
x_306 = l_Lean_Expr_isConstOf(x_304, x_305);
lean_dec_ref(x_304);
if (x_306 == 0)
{
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_free_object(x_277);
x_281 = x_2;
x_282 = x_3;
x_283 = x_4;
x_284 = x_5;
x_285 = x_6;
x_286 = x_7;
x_287 = x_8;
x_288 = x_9;
goto block_291;
}
else
{
uint8_t x_307; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc_ref(x_1);
x_307 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_308 = lean_unsigned_to_nat(2u);
x_309 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set_uint8(x_309, sizeof(void*)*1, x_307);
lean_ctor_set_uint8(x_309, sizeof(void*)*1 + 1, x_307);
lean_ctor_set(x_277, 0, x_309);
return x_277;
}
else
{
lean_object* x_310; 
lean_free_object(x_277);
x_310 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(x_1, x_297, x_296, x_2, x_4, x_8, x_9, x_280);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_310;
}
}
}
}
else
{
lean_object* x_311; 
lean_dec_ref(x_298);
lean_free_object(x_277);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_311 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(x_1, x_297, x_296, x_2, x_4, x_8, x_9, x_280);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_311;
}
}
else
{
lean_object* x_312; 
lean_dec_ref(x_298);
lean_free_object(x_277);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_312 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(x_1, x_297, x_296, x_2, x_4, x_8, x_9, x_280);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_312;
}
}
}
block_291:
{
uint8_t x_289; 
x_289 = l_Lean_Meta_Grind_isIte(x_1);
if (x_289 == 0)
{
uint8_t x_290; 
x_290 = l_Lean_Meta_Grind_isDIte(x_1);
x_117 = x_283;
x_118 = x_287;
x_119 = x_284;
x_120 = x_281;
x_121 = x_285;
x_122 = x_280;
x_123 = x_288;
x_124 = x_286;
x_125 = x_282;
x_126 = x_290;
goto block_276;
}
else
{
x_117 = x_283;
x_118 = x_287;
x_119 = x_284;
x_120 = x_281;
x_121 = x_285;
x_122 = x_280;
x_123 = x_288;
x_124 = x_286;
x_125 = x_282;
x_126 = x_289;
goto block_276;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_326; uint8_t x_327; 
x_313 = lean_ctor_get(x_277, 0);
x_314 = lean_ctor_get(x_277, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_277);
x_326 = l_Lean_Expr_cleanupAnnotations(x_313);
x_327 = l_Lean_Expr_isApp(x_326);
if (x_327 == 0)
{
lean_dec_ref(x_326);
x_315 = x_2;
x_316 = x_3;
x_317 = x_4;
x_318 = x_5;
x_319 = x_6;
x_320 = x_7;
x_321 = x_8;
x_322 = x_9;
goto block_325;
}
else
{
lean_object* x_328; uint8_t x_329; 
lean_inc_ref(x_326);
x_328 = l_Lean_Expr_appFnCleanup___redArg(x_326);
x_329 = l_Lean_Expr_isApp(x_328);
if (x_329 == 0)
{
lean_dec_ref(x_328);
lean_dec_ref(x_326);
x_315 = x_2;
x_316 = x_3;
x_317 = x_4;
x_318 = x_5;
x_319 = x_6;
x_320 = x_7;
x_321 = x_8;
x_322 = x_9;
goto block_325;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_330 = lean_ctor_get(x_326, 1);
lean_inc_ref(x_330);
lean_dec_ref(x_326);
x_331 = lean_ctor_get(x_328, 1);
lean_inc_ref(x_331);
x_332 = l_Lean_Expr_appFnCleanup___redArg(x_328);
x_333 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_334 = l_Lean_Expr_isConstOf(x_332, x_333);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
x_336 = l_Lean_Expr_isConstOf(x_332, x_335);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = l_Lean_Expr_isApp(x_332);
if (x_337 == 0)
{
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec_ref(x_330);
x_315 = x_2;
x_316 = x_3;
x_317 = x_4;
x_318 = x_5;
x_319 = x_6;
x_320 = x_7;
x_321 = x_8;
x_322 = x_9;
goto block_325;
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = l_Lean_Expr_appFnCleanup___redArg(x_332);
x_339 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
x_340 = l_Lean_Expr_isConstOf(x_338, x_339);
lean_dec_ref(x_338);
if (x_340 == 0)
{
lean_dec_ref(x_331);
lean_dec_ref(x_330);
x_315 = x_2;
x_316 = x_3;
x_317 = x_4;
x_318 = x_5;
x_319 = x_6;
x_320 = x_7;
x_321 = x_8;
x_322 = x_9;
goto block_325;
}
else
{
uint8_t x_341; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc_ref(x_1);
x_341 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec_ref(x_331);
lean_dec_ref(x_330);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_342 = lean_unsigned_to_nat(2u);
x_343 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set_uint8(x_343, sizeof(void*)*1, x_341);
lean_ctor_set_uint8(x_343, sizeof(void*)*1 + 1, x_341);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_314);
return x_344;
}
else
{
lean_object* x_345; 
x_345 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(x_1, x_331, x_330, x_2, x_4, x_8, x_9, x_314);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_345;
}
}
}
}
else
{
lean_object* x_346; 
lean_dec_ref(x_332);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_346 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(x_1, x_331, x_330, x_2, x_4, x_8, x_9, x_314);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_346;
}
}
else
{
lean_object* x_347; 
lean_dec_ref(x_332);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_347 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(x_1, x_331, x_330, x_2, x_4, x_8, x_9, x_314);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_347;
}
}
}
block_325:
{
uint8_t x_323; 
x_323 = l_Lean_Meta_Grind_isIte(x_1);
if (x_323 == 0)
{
uint8_t x_324; 
x_324 = l_Lean_Meta_Grind_isDIte(x_1);
x_117 = x_317;
x_118 = x_321;
x_119 = x_318;
x_120 = x_315;
x_121 = x_319;
x_122 = x_314;
x_123 = x_322;
x_124 = x_320;
x_125 = x_316;
x_126 = x_324;
goto block_276;
}
else
{
x_117 = x_317;
x_118 = x_321;
x_119 = x_318;
x_120 = x_315;
x_121 = x_319;
x_122 = x_314;
x_123 = x_322;
x_124 = x_320;
x_125 = x_316;
x_126 = x_323;
goto block_276;
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_348 = !lean_is_exclusive(x_277);
if (x_348 == 0)
{
return x_277;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_277, 0);
x_350 = lean_ctor_get(x_277, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_277);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
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
block_116:
{
uint8_t x_33; 
x_33 = l_Lean_Expr_isFVar(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_1);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; 
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc_ref(x_1);
x_36 = lean_infer_type(x_1, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_39 = l_Lean_Meta_whnfD(x_37, x_28, x_29, x_30, x_31, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_Expr_getAppFn(x_40);
if (lean_obj_tag(x_42) == 4)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc_ref(x_30);
x_44 = l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(x_43, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_41);
lean_dec(x_24);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 5)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
lean_dec_ref(x_45);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_44, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_46, 4);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_46, sizeof(void*)*6);
lean_dec_ref(x_46);
x_51 = l_List_lengthTR___redArg(x_49);
lean_dec(x_49);
x_52 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1 + 1, x_23);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_ctor_get(x_46, 4);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_46, sizeof(void*)*6);
lean_dec_ref(x_46);
x_56 = l_List_lengthTR___redArg(x_54);
lean_dec(x_54);
x_57 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1 + 1, x_23);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_45);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec_ref(x_44);
x_60 = l_Lean_Meta_Grind_getConfig___redArg(x_26, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*8 + 11);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec_ref(x_60);
x_15 = x_63;
goto block_18;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec_ref(x_60);
x_65 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
x_66 = l_Lean_MessageData_ofExpr(x_1);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_indentExpr(x_40);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_Grind_reportIssue(x_71, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_64);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_15 = x_73;
goto block_18;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_60;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_60, 0);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_60);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_44);
if (x_82 == 0)
{
return x_44;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_44, 0);
x_84 = lean_ctor_get(x_44, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_44);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec_ref(x_42);
lean_dec(x_24);
x_86 = l_Lean_Meta_Grind_getConfig___redArg(x_26, x_41);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_87, sizeof(void*)*8 + 11);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec_ref(x_86);
x_19 = x_89;
goto block_22;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec_ref(x_86);
x_91 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
x_92 = l_Lean_MessageData_ofExpr(x_1);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_indentExpr(x_40);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Meta_Grind_reportIssue(x_97, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_90);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_19 = x_99;
goto block_22;
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_104 = !lean_is_exclusive(x_86);
if (x_104 == 0)
{
return x_86;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_86, 0);
x_106 = lean_ctor_get(x_86, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_86);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_1);
x_108 = !lean_is_exclusive(x_39);
if (x_108 == 0)
{
return x_39;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_39, 0);
x_110 = lean_ctor_get(x_39, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_39);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_36);
if (x_112 == 0)
{
return x_36;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_36, 0);
x_114 = lean_ctor_get(x_36, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_36);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
block_276:
{
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(x_1, x_120, x_122);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec_ref(x_127);
lean_inc(x_123);
lean_inc_ref(x_118);
lean_inc(x_124);
lean_inc_ref(x_121);
lean_inc(x_119);
lean_inc_ref(x_117);
lean_inc(x_125);
lean_inc(x_120);
lean_inc_ref(x_1);
x_131 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(x_1, x_120, x_125, x_117, x_119, x_121, x_124, x_118, x_123, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_131, 1);
x_136 = lean_ctor_get(x_131, 0);
lean_dec(x_136);
x_137 = lean_st_ref_get(x_123, x_135);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc_ref(x_140);
lean_dec(x_138);
x_141 = l_Lean_Meta_isMatcherAppCore_x3f(x_140, x_1);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
lean_free_object(x_131);
x_142 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_142) == 4)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc(x_123);
lean_inc_ref(x_118);
lean_inc(x_124);
lean_inc_ref(x_121);
x_144 = l_Lean_Meta_isInductivePredicate_x3f(x_143, x_121, x_124, x_118, x_123, x_139);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_unbox(x_132);
lean_dec(x_132);
x_23 = x_147;
x_24 = x_120;
x_25 = x_125;
x_26 = x_117;
x_27 = x_119;
x_28 = x_121;
x_29 = x_124;
x_30 = x_118;
x_31 = x_123;
x_32 = x_146;
goto block_116;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec_ref(x_144);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
lean_dec_ref(x_145);
lean_inc_ref(x_1);
x_150 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_120, x_117, x_118, x_123, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
lean_dec(x_149);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec_ref(x_150);
x_154 = lean_unbox(x_132);
lean_dec(x_132);
x_23 = x_154;
x_24 = x_120;
x_25 = x_125;
x_26 = x_117;
x_27 = x_119;
x_28 = x_121;
x_29 = x_124;
x_30 = x_118;
x_31 = x_123;
x_32 = x_153;
goto block_116;
}
else
{
uint8_t x_155; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_155 = !lean_is_exclusive(x_150);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_150, 0);
lean_dec(x_156);
x_157 = lean_ctor_get(x_149, 4);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_149, sizeof(void*)*6);
lean_dec(x_149);
x_159 = l_List_lengthTR___redArg(x_157);
lean_dec(x_157);
x_160 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_158);
x_161 = lean_unbox(x_132);
lean_dec(x_132);
lean_ctor_set_uint8(x_160, sizeof(void*)*1 + 1, x_161);
lean_ctor_set(x_150, 0, x_160);
return x_150;
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
lean_dec(x_150);
x_163 = lean_ctor_get(x_149, 4);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_149, sizeof(void*)*6);
lean_dec(x_149);
x_165 = l_List_lengthTR___redArg(x_163);
lean_dec(x_163);
x_166 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_164);
x_167 = lean_unbox(x_132);
lean_dec(x_132);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 1, x_167);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_162);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_149);
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_169 = !lean_is_exclusive(x_150);
if (x_169 == 0)
{
return x_150;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_150, 0);
x_171 = lean_ctor_get(x_150, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_150);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_173 = !lean_is_exclusive(x_144);
if (x_173 == 0)
{
return x_144;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_144, 0);
x_175 = lean_ctor_get(x_144, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_144);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec_ref(x_142);
x_177 = lean_unbox(x_132);
lean_dec(x_132);
x_23 = x_177;
x_24 = x_120;
x_25 = x_125;
x_26 = x_117;
x_27 = x_119;
x_28 = x_121;
x_29 = x_124;
x_30 = x_118;
x_31 = x_123;
x_32 = x_139;
goto block_116;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_141, 0);
lean_inc(x_178);
lean_dec_ref(x_141);
x_179 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_178);
lean_dec(x_178);
x_180 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_unbox(x_132);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_181);
x_182 = lean_unbox(x_132);
lean_dec(x_132);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 1, x_182);
lean_ctor_set(x_131, 1, x_139);
lean_ctor_set(x_131, 0, x_180);
return x_131;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_183 = lean_ctor_get(x_131, 1);
lean_inc(x_183);
lean_dec(x_131);
x_184 = lean_st_ref_get(x_123, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc_ref(x_187);
lean_dec(x_185);
x_188 = l_Lean_Meta_isMatcherAppCore_x3f(x_187, x_1);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_189) == 4)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
lean_inc(x_123);
lean_inc_ref(x_118);
lean_inc(x_124);
lean_inc_ref(x_121);
x_191 = l_Lean_Meta_isInductivePredicate_x3f(x_190, x_121, x_124, x_118, x_123, x_186);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec_ref(x_191);
x_194 = lean_unbox(x_132);
lean_dec(x_132);
x_23 = x_194;
x_24 = x_120;
x_25 = x_125;
x_26 = x_117;
x_27 = x_119;
x_28 = x_121;
x_29 = x_124;
x_30 = x_118;
x_31 = x_123;
x_32 = x_193;
goto block_116;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec_ref(x_191);
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec_ref(x_192);
lean_inc_ref(x_1);
x_197 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_120, x_117, x_118, x_123, x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
lean_dec(x_196);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec_ref(x_197);
x_201 = lean_unbox(x_132);
lean_dec(x_132);
x_23 = x_201;
x_24 = x_120;
x_25 = x_125;
x_26 = x_117;
x_27 = x_119;
x_28 = x_121;
x_29 = x_124;
x_30 = x_118;
x_31 = x_123;
x_32 = x_200;
goto block_116;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_196, 4);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_196, sizeof(void*)*6);
lean_dec(x_196);
x_206 = l_List_lengthTR___redArg(x_204);
lean_dec(x_204);
x_207 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*1, x_205);
x_208 = lean_unbox(x_132);
lean_dec(x_132);
lean_ctor_set_uint8(x_207, sizeof(void*)*1 + 1, x_208);
if (lean_is_scalar(x_203)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_203;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_202);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_196);
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_210 = lean_ctor_get(x_197, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_212 = x_197;
} else {
 lean_dec_ref(x_197);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_214 = lean_ctor_get(x_191, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_191, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_216 = x_191;
} else {
 lean_dec_ref(x_191);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
uint8_t x_218; 
lean_dec_ref(x_189);
x_218 = lean_unbox(x_132);
lean_dec(x_132);
x_23 = x_218;
x_24 = x_120;
x_25 = x_125;
x_26 = x_117;
x_27 = x_119;
x_28 = x_121;
x_29 = x_124;
x_30 = x_118;
x_31 = x_123;
x_32 = x_186;
goto block_116;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_219 = lean_ctor_get(x_188, 0);
lean_inc(x_219);
lean_dec_ref(x_188);
x_220 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_219);
lean_dec(x_219);
x_221 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_unbox(x_132);
lean_ctor_set_uint8(x_221, sizeof(void*)*1, x_222);
x_223 = lean_unbox(x_132);
lean_dec(x_132);
lean_ctor_set_uint8(x_221, sizeof(void*)*1 + 1, x_223);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_186);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_225 = !lean_is_exclusive(x_131);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_131, 0);
lean_dec(x_226);
x_227 = lean_box(0);
lean_ctor_set(x_131, 0, x_227);
return x_131;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_131, 1);
lean_inc(x_228);
lean_dec(x_131);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_231 = !lean_is_exclusive(x_131);
if (x_231 == 0)
{
return x_131;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_131, 0);
x_233 = lean_ctor_get(x_131, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_131);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_127, 1);
lean_inc(x_235);
lean_dec_ref(x_127);
x_236 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7;
x_237 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(x_236, x_118, x_235);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_unbox(x_238);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec_ref(x_237);
x_11 = x_240;
goto block_14;
}
else
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_237);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_237, 1);
x_243 = lean_ctor_get(x_237, 0);
lean_dec(x_243);
x_244 = l_Lean_Meta_Grind_updateLastTag(x_120, x_125, x_117, x_119, x_121, x_124, x_118, x_123, x_242);
lean_dec(x_119);
lean_dec_ref(x_117);
lean_dec(x_125);
lean_dec(x_120);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec_ref(x_244);
x_246 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
x_247 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_237, 7);
lean_ctor_set(x_237, 1, x_247);
lean_ctor_set(x_237, 0, x_246);
x_248 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_236, x_237, x_121, x_124, x_118, x_123, x_245);
lean_dec(x_123);
lean_dec_ref(x_118);
lean_dec(x_124);
lean_dec_ref(x_121);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec_ref(x_248);
x_11 = x_249;
goto block_14;
}
else
{
uint8_t x_250; 
lean_free_object(x_237);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec_ref(x_118);
lean_dec_ref(x_1);
x_250 = !lean_is_exclusive(x_244);
if (x_250 == 0)
{
return x_244;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_244, 0);
x_252 = lean_ctor_get(x_244, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_244);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_237, 1);
lean_inc(x_254);
lean_dec(x_237);
x_255 = l_Lean_Meta_Grind_updateLastTag(x_120, x_125, x_117, x_119, x_121, x_124, x_118, x_123, x_254);
lean_dec(x_119);
lean_dec_ref(x_117);
lean_dec(x_125);
lean_dec(x_120);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
x_258 = l_Lean_MessageData_ofExpr(x_1);
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_236, x_259, x_121, x_124, x_118, x_123, x_256);
lean_dec(x_123);
lean_dec_ref(x_118);
lean_dec(x_124);
lean_dec_ref(x_121);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec_ref(x_260);
x_11 = x_261;
goto block_14;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec_ref(x_118);
lean_dec_ref(x_1);
x_262 = lean_ctor_get(x_255, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_255, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_264 = x_255;
} else {
 lean_dec_ref(x_255);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec_ref(x_1);
x_266 = !lean_is_exclusive(x_127);
if (x_266 == 0)
{
return x_127;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_127, 0);
x_268 = lean_ctor_get(x_127, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_127);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec_ref(x_121);
lean_dec(x_119);
x_270 = lean_unsigned_to_nat(1u);
x_271 = l_Lean_Expr_getAppNumArgs(x_1);
x_272 = lean_nat_sub(x_271, x_270);
lean_dec(x_271);
x_273 = lean_nat_sub(x_272, x_270);
lean_dec(x_272);
x_274 = l_Lean_Expr_getRevArg_x21(x_1, x_273);
lean_dec_ref(x_1);
x_275 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(x_274, x_120, x_117, x_118, x_123, x_122);
lean_dec(x_123);
lean_dec_ref(x_118);
lean_dec_ref(x_117);
lean_dec(x_120);
return x_275;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("may be irrelevant\na: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nb: ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\neq: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\narg_a: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\narg_b: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", gen: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_46; uint8_t x_162; 
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
x_162 = l_Lean_Expr_isApp(x_19);
if (x_162 == 0)
{
x_46 = x_162;
goto block_161;
}
else
{
uint8_t x_163; 
x_163 = l_Lean_Expr_isApp(x_21);
x_46 = x_163;
goto block_161;
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 1, x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_24);
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
lean_dec_ref(x_37);
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
block_161:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
x_56 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0;
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_Expr_appArg_x21(x_19);
x_60 = l_Lean_Expr_appArg_x21(x_21);
x_61 = l_Lean_Meta_Grind_isEqv___redArg(x_59, x_60, x_7, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
x_65 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
x_66 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(x_65, x_13, x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_55;
x_25 = x_46;
x_26 = x_70;
x_27 = x_69;
goto block_35;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
x_73 = lean_ctor_get(x_66, 0);
lean_dec(x_73);
x_74 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_80 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_80);
lean_ctor_set(x_66, 0, x_79);
x_81 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_66);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_MessageData_ofExpr(x_5);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_MessageData_ofExpr(x_3);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_MessageData_ofExpr(x_59);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_MessageData_ofExpr(x_60);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Nat_reprFast(x_77);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_65, x_102, x_11, x_12, x_13, x_14, x_78);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_55;
x_25 = x_46;
x_26 = x_105;
x_27 = x_104;
goto block_35;
}
else
{
uint8_t x_106; 
lean_free_object(x_66);
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_106 = !lean_is_exclusive(x_76);
if (x_106 == 0)
{
return x_76;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_76, 0);
x_108 = lean_ctor_get(x_76, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_76);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_66);
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_110 = !lean_is_exclusive(x_74);
if (x_110 == 0)
{
return x_74;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_74, 0);
x_112 = lean_ctor_get(x_74, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_74);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_66, 1);
lean_inc(x_114);
lean_dec(x_66);
x_115 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_121 = l_Lean_MessageData_ofExpr(x_4);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_MessageData_ofExpr(x_5);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_MessageData_ofExpr(x_3);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_MessageData_ofExpr(x_59);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_MessageData_ofExpr(x_60);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Nat_reprFast(x_118);
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_MessageData_ofFormat(x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_65, x_144, x_11, x_12, x_13, x_14, x_119);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_55;
x_25 = x_46;
x_26 = x_147;
x_27 = x_146;
goto block_35;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_148 = lean_ctor_get(x_117, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_117, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_150 = x_117;
} else {
 lean_dec_ref(x_117);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_152 = lean_ctor_get(x_115, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_115, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_154 = x_115;
} else {
 lean_dec_ref(x_115);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_156 = lean_ctor_get(x_61, 1);
lean_inc(x_156);
lean_dec_ref(x_61);
x_36 = x_55;
x_37 = x_19;
x_38 = x_156;
goto block_45;
}
}
else
{
uint8_t x_157; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_61);
if (x_157 == 0)
{
return x_61;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_61, 0);
x_159 = lean_ctor_get(x_61, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_61);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_46; uint8_t x_162; 
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
x_162 = l_Lean_Expr_isApp(x_19);
if (x_162 == 0)
{
x_46 = x_162;
goto block_161;
}
else
{
uint8_t x_163; 
x_163 = l_Lean_Expr_isApp(x_21);
x_46 = x_163;
goto block_161;
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
lean_dec_ref(x_37);
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
x_44 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_38);
return x_44;
}
block_161:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
x_56 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0;
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_Expr_appArg_x21(x_19);
x_60 = l_Lean_Expr_appArg_x21(x_21);
x_61 = l_Lean_Meta_Grind_isEqv___redArg(x_59, x_60, x_7, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
x_65 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
x_66 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(x_65, x_13, x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_70;
x_25 = x_46;
x_26 = x_55;
x_27 = x_69;
goto block_35;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
x_73 = lean_ctor_get(x_66, 0);
lean_dec(x_73);
x_74 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_80 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_80);
lean_ctor_set(x_66, 0, x_79);
x_81 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_66);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_MessageData_ofExpr(x_5);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_MessageData_ofExpr(x_3);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_MessageData_ofExpr(x_59);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_MessageData_ofExpr(x_60);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Nat_reprFast(x_77);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_65, x_102, x_11, x_12, x_13, x_14, x_78);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_105;
x_25 = x_46;
x_26 = x_55;
x_27 = x_104;
goto block_35;
}
else
{
uint8_t x_106; 
lean_free_object(x_66);
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_106 = !lean_is_exclusive(x_76);
if (x_106 == 0)
{
return x_76;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_76, 0);
x_108 = lean_ctor_get(x_76, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_76);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_66);
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_110 = !lean_is_exclusive(x_74);
if (x_110 == 0)
{
return x_74;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_74, 0);
x_112 = lean_ctor_get(x_74, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_74);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_66, 1);
lean_inc(x_114);
lean_dec(x_66);
x_115 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_121 = l_Lean_MessageData_ofExpr(x_4);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_MessageData_ofExpr(x_5);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_MessageData_ofExpr(x_3);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_MessageData_ofExpr(x_59);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_MessageData_ofExpr(x_60);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Nat_reprFast(x_118);
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_MessageData_ofFormat(x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_65, x_144, x_11, x_12, x_13, x_14, x_119);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_147;
x_25 = x_46;
x_26 = x_55;
x_27 = x_146;
goto block_35;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_148 = lean_ctor_get(x_117, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_117, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_150 = x_117;
} else {
 lean_dec_ref(x_117);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_152 = lean_ctor_get(x_115, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_115, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_154 = x_115;
} else {
 lean_dec_ref(x_115);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_156 = lean_ctor_get(x_61, 1);
lean_inc(x_156);
lean_dec_ref(x_61);
x_36 = x_55;
x_37 = x_19;
x_38 = x_156;
goto block_45;
}
}
else
{
uint8_t x_157; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_61);
if (x_157 == 0)
{
return x_61;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_61, 0);
x_159 = lean_ctor_get(x_61, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_61);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_expr_eqv(x_11, x_13);
if (x_15 == 0)
{
x_7 = x_15;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_expr_eqv(x_12, x_14);
x_7 = x_16;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_3);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = l_Lean_Expr_hash(x_5);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg(x_2, x_21);
lean_dec(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_43; lean_object* x_78; 
lean_inc_ref(x_3);
x_78 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_6, x_10, x_11, x_12);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec_ref(x_78);
lean_inc_ref(x_3);
x_82 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_6, x_10, x_11, x_81);
x_43 = x_82;
goto block_77;
}
else
{
x_43 = x_78;
goto block_77;
}
}
else
{
x_43 = x_78;
goto block_77;
}
block_42:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = l_Lean_Expr_getAppNumArgs(x_1);
x_17 = lean_box(0);
lean_inc_ref(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_inc_ref(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(x_17, x_15, x_3, x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
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
lean_dec_ref(x_23);
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
lean_dec_ref(x_23);
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
block_77:
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec_ref(x_43);
x_47 = lean_st_ref_get(x_4, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 14);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 1);
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_49, 7);
lean_inc_ref(x_53);
lean_dec_ref(x_49);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
lean_ctor_set(x_47, 1, x_2);
lean_ctor_set(x_47, 0, x_1);
x_54 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg(x_53, x_47);
lean_dec_ref(x_47);
lean_dec_ref(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_box(0);
x_56 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_56;
x_14 = x_51;
x_15 = x_55;
goto block_42;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec_ref(x_54);
x_58 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_58;
x_14 = x_51;
x_15 = x_57;
goto block_42;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_dec(x_47);
x_60 = lean_ctor_get(x_49, 7);
lean_inc_ref(x_60);
lean_dec_ref(x_49);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
x_62 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg(x_60, x_61);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_box(0);
x_64 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_64;
x_14 = x_59;
x_15 = x_63;
goto block_42;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec_ref(x_62);
x_66 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_66;
x_14 = x_59;
x_15 = x_65;
goto block_42;
}
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_43, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_43, 0, x_69);
return x_43;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_43, 1);
lean_inc(x_70);
lean_dec(x_43);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_43);
if (x_73 == 0)
{
return x_43;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_43, 0);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args) {
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
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_checkSplitInfoArgStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; uint8_t x_13; lean_object* x_14; lean_object* x_29; 
lean_inc_ref(x_1);
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
lean_dec_ref(x_29);
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
lean_dec_ref(x_29);
x_53 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_54);
lean_dec_ref(x_1);
lean_inc_ref(x_53);
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
lean_dec_ref(x_80);
x_84 = l_Lean_Meta_Grind_isEqFalse___redArg(x_53, x_2, x_3, x_4, x_5, x_83);
x_55 = x_84;
goto block_79;
}
else
{
lean_dec_ref(x_53);
x_55 = x_80;
goto block_79;
}
}
else
{
lean_dec_ref(x_53);
x_55 = x_80;
goto block_79;
}
block_79:
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec_ref(x_55);
x_59 = l_Lean_Expr_hasLooseBVars(x_54);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc_ref(x_54);
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
lean_dec_ref(x_60);
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
lean_dec_ref(x_54);
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
lean_dec_ref(x_54);
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
lean_dec_ref(x_54);
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
lean_dec_ref(x_54);
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
lean_dec_ref(x_54);
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
lean_dec_ref(x_1);
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
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
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
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(x_13, x_2, x_4, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = l_Lean_Meta_Grind_checkSplitInfoArgStatus(x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
lean_dec_ref(x_1);
x_7 = lean_box(x_5);
x_8 = lean_box(x_6);
x_9 = lean_apply_4(x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(x_2, x_4);
return x_5;
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 14);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 14);
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_139; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec_ref(x_22);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_30 = lean_st_ref_get(x_4, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_133 = lean_ctor_get(x_31, 14);
lean_inc_ref(x_133);
lean_dec(x_31);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_dec_lt(x_135, x_28);
if (x_139 == 0)
{
x_136 = x_29;
goto block_138;
}
else
{
x_136 = x_139;
goto block_138;
}
block_132:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_st_ref_take(x_4, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 12);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_35, 14);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec_ref(x_34);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_35, 14);
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
lean_ctor_set(x_35, 14, x_61);
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
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_37, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_37, 3);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_37, 4);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_37, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_37, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_37, 7);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_37, 8);
lean_inc_ref(x_81);
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
lean_ctor_set(x_35, 14, x_85);
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
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_90 = lean_ctor_get(x_35, 0);
x_91 = lean_ctor_get(x_35, 1);
x_92 = lean_ctor_get(x_35, 2);
x_93 = lean_ctor_get(x_35, 3);
x_94 = lean_ctor_get(x_35, 4);
x_95 = lean_ctor_get(x_35, 5);
x_96 = lean_ctor_get(x_35, 6);
x_97 = lean_ctor_get(x_35, 7);
x_98 = lean_ctor_get_uint8(x_35, sizeof(void*)*17);
x_99 = lean_ctor_get(x_35, 8);
x_100 = lean_ctor_get(x_35, 9);
x_101 = lean_ctor_get(x_35, 10);
x_102 = lean_ctor_get(x_35, 11);
x_103 = lean_ctor_get(x_35, 13);
x_104 = lean_ctor_get(x_35, 15);
x_105 = lean_ctor_get(x_35, 16);
lean_inc(x_105);
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
x_106 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_36, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_36, 2);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_36, 3);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_36, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_36, 6);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_36, 7);
lean_inc(x_112);
x_113 = lean_ctor_get(x_36, 8);
lean_inc_ref(x_113);
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
 x_114 = x_36;
} else {
 lean_dec_ref(x_36);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_37, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_37, 3);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_37, 4);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_37, 5);
lean_inc(x_119);
x_120 = lean_ctor_get(x_37, 6);
lean_inc(x_120);
x_121 = lean_ctor_get(x_37, 7);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_37, 8);
lean_inc_ref(x_122);
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
 x_123 = x_37;
} else {
 lean_dec_ref(x_37);
 x_123 = lean_box(0);
}
x_124 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_114)) {
 x_125 = lean_alloc_ctor(0, 9, 0);
} else {
 x_125 = x_114;
}
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_107);
lean_ctor_set(x_125, 2, x_108);
lean_ctor_set(x_125, 3, x_109);
lean_ctor_set(x_125, 4, x_110);
lean_ctor_set(x_125, 5, x_124);
lean_ctor_set(x_125, 6, x_111);
lean_ctor_set(x_125, 7, x_112);
lean_ctor_set(x_125, 8, x_113);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 9, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_33);
lean_ctor_set(x_126, 1, x_115);
lean_ctor_set(x_126, 2, x_116);
lean_ctor_set(x_126, 3, x_117);
lean_ctor_set(x_126, 4, x_118);
lean_ctor_set(x_126, 5, x_119);
lean_ctor_set(x_126, 6, x_120);
lean_ctor_set(x_126, 7, x_121);
lean_ctor_set(x_126, 8, x_122);
x_127 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_127, 0, x_90);
lean_ctor_set(x_127, 1, x_91);
lean_ctor_set(x_127, 2, x_92);
lean_ctor_set(x_127, 3, x_93);
lean_ctor_set(x_127, 4, x_94);
lean_ctor_set(x_127, 5, x_95);
lean_ctor_set(x_127, 6, x_96);
lean_ctor_set(x_127, 7, x_97);
lean_ctor_set(x_127, 8, x_99);
lean_ctor_set(x_127, 9, x_100);
lean_ctor_set(x_127, 10, x_101);
lean_ctor_set(x_127, 11, x_102);
lean_ctor_set(x_127, 12, x_125);
lean_ctor_set(x_127, 13, x_103);
lean_ctor_set(x_127, 14, x_126);
lean_ctor_set(x_127, 15, x_104);
lean_ctor_set(x_127, 16, x_105);
lean_ctor_set_uint8(x_127, sizeof(void*)*17, x_98);
x_128 = lean_st_ref_set(x_4, x_127, x_38);
lean_dec(x_4);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_2);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
block_138:
{
if (x_136 == 0)
{
x_33 = x_134;
goto block_132;
}
else
{
lean_object* x_137; 
x_137 = lean_nat_add(x_134, x_135);
lean_dec(x_134);
x_33 = x_137;
goto block_132;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_140 = lean_ctor_get(x_15, 0);
x_141 = lean_ctor_get(x_15, 1);
x_142 = lean_ctor_get(x_15, 3);
x_143 = lean_ctor_get(x_15, 4);
x_144 = lean_ctor_get(x_15, 5);
x_145 = lean_ctor_get(x_15, 6);
x_146 = lean_ctor_get(x_15, 7);
x_147 = lean_ctor_get(x_15, 8);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_15);
x_148 = l_List_reverse___redArg(x_3);
x_149 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_149, 0, x_140);
lean_ctor_set(x_149, 1, x_141);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_142);
lean_ctor_set(x_149, 4, x_143);
lean_ctor_set(x_149, 5, x_144);
lean_ctor_set(x_149, 6, x_145);
lean_ctor_set(x_149, 7, x_146);
lean_ctor_set(x_149, 8, x_147);
lean_ctor_set(x_14, 14, x_149);
x_150 = lean_st_ref_set(x_4, x_14, x_16);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_4);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_2);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_216; 
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec_ref(x_150);
x_155 = lean_ctor_get(x_2, 1);
x_156 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_157 = lean_st_ref_get(x_4, x_154);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_210 = lean_ctor_get(x_158, 14);
lean_inc_ref(x_210);
lean_dec(x_158);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_unsigned_to_nat(1u);
x_216 = lean_nat_dec_lt(x_212, x_155);
if (x_216 == 0)
{
x_213 = x_156;
goto block_215;
}
else
{
x_213 = x_216;
goto block_215;
}
block_209:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_161 = lean_st_ref_take(x_4, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 12);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_162, 14);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec_ref(x_161);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_162, 2);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_162, 3);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_162, 4);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_162, 5);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_162, 6);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_162, 7);
lean_inc_ref(x_173);
x_174 = lean_ctor_get_uint8(x_162, sizeof(void*)*17);
x_175 = lean_ctor_get(x_162, 8);
lean_inc(x_175);
x_176 = lean_ctor_get(x_162, 9);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_162, 10);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_162, 11);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_162, 13);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_162, 15);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_162, 16);
lean_inc_ref(x_181);
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
 lean_ctor_release(x_162, 9);
 lean_ctor_release(x_162, 10);
 lean_ctor_release(x_162, 11);
 lean_ctor_release(x_162, 12);
 lean_ctor_release(x_162, 13);
 lean_ctor_release(x_162, 14);
 lean_ctor_release(x_162, 15);
 lean_ctor_release(x_162, 16);
 x_182 = x_162;
} else {
 lean_dec_ref(x_162);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_163, 0);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_163, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_163, 2);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_163, 3);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_163, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_163, 6);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_163, 7);
lean_inc(x_189);
x_190 = lean_ctor_get(x_163, 8);
lean_inc_ref(x_190);
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
 x_191 = x_163;
} else {
 lean_dec_ref(x_163);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_164, 1);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_164, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_164, 3);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_164, 4);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_164, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_164, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_164, 7);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_164, 8);
lean_inc_ref(x_199);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 lean_ctor_release(x_164, 6);
 lean_ctor_release(x_164, 7);
 lean_ctor_release(x_164, 8);
 x_200 = x_164;
} else {
 lean_dec_ref(x_164);
 x_200 = lean_box(0);
}
x_201 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_191)) {
 x_202 = lean_alloc_ctor(0, 9, 0);
} else {
 x_202 = x_191;
}
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_184);
lean_ctor_set(x_202, 2, x_185);
lean_ctor_set(x_202, 3, x_186);
lean_ctor_set(x_202, 4, x_187);
lean_ctor_set(x_202, 5, x_201);
lean_ctor_set(x_202, 6, x_188);
lean_ctor_set(x_202, 7, x_189);
lean_ctor_set(x_202, 8, x_190);
if (lean_is_scalar(x_200)) {
 x_203 = lean_alloc_ctor(0, 9, 0);
} else {
 x_203 = x_200;
}
lean_ctor_set(x_203, 0, x_160);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_193);
lean_ctor_set(x_203, 3, x_194);
lean_ctor_set(x_203, 4, x_195);
lean_ctor_set(x_203, 5, x_196);
lean_ctor_set(x_203, 6, x_197);
lean_ctor_set(x_203, 7, x_198);
lean_ctor_set(x_203, 8, x_199);
if (lean_is_scalar(x_182)) {
 x_204 = lean_alloc_ctor(0, 17, 1);
} else {
 x_204 = x_182;
}
lean_ctor_set(x_204, 0, x_166);
lean_ctor_set(x_204, 1, x_167);
lean_ctor_set(x_204, 2, x_168);
lean_ctor_set(x_204, 3, x_169);
lean_ctor_set(x_204, 4, x_170);
lean_ctor_set(x_204, 5, x_171);
lean_ctor_set(x_204, 6, x_172);
lean_ctor_set(x_204, 7, x_173);
lean_ctor_set(x_204, 8, x_175);
lean_ctor_set(x_204, 9, x_176);
lean_ctor_set(x_204, 10, x_177);
lean_ctor_set(x_204, 11, x_178);
lean_ctor_set(x_204, 12, x_202);
lean_ctor_set(x_204, 13, x_179);
lean_ctor_set(x_204, 14, x_203);
lean_ctor_set(x_204, 15, x_180);
lean_ctor_set(x_204, 16, x_181);
lean_ctor_set_uint8(x_204, sizeof(void*)*17, x_174);
x_205 = lean_st_ref_set(x_4, x_204, x_165);
lean_dec(x_4);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_2);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
block_215:
{
if (x_213 == 0)
{
x_160 = x_211;
goto block_209;
}
else
{
lean_object* x_214; 
x_214 = lean_nat_add(x_211, x_212);
lean_dec(x_211);
x_160 = x_214;
goto block_209;
}
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_217 = lean_ctor_get(x_14, 0);
x_218 = lean_ctor_get(x_14, 1);
x_219 = lean_ctor_get(x_14, 2);
x_220 = lean_ctor_get(x_14, 3);
x_221 = lean_ctor_get(x_14, 4);
x_222 = lean_ctor_get(x_14, 5);
x_223 = lean_ctor_get(x_14, 6);
x_224 = lean_ctor_get(x_14, 7);
x_225 = lean_ctor_get_uint8(x_14, sizeof(void*)*17);
x_226 = lean_ctor_get(x_14, 8);
x_227 = lean_ctor_get(x_14, 9);
x_228 = lean_ctor_get(x_14, 10);
x_229 = lean_ctor_get(x_14, 11);
x_230 = lean_ctor_get(x_14, 12);
x_231 = lean_ctor_get(x_14, 13);
x_232 = lean_ctor_get(x_14, 15);
x_233 = lean_ctor_get(x_14, 16);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_14);
x_234 = lean_ctor_get(x_15, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_15, 5);
lean_inc(x_238);
x_239 = lean_ctor_get(x_15, 6);
lean_inc(x_239);
x_240 = lean_ctor_get(x_15, 7);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_15, 8);
lean_inc_ref(x_241);
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
 x_242 = x_15;
} else {
 lean_dec_ref(x_15);
 x_242 = lean_box(0);
}
x_243 = l_List_reverse___redArg(x_3);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 9, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_235);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_236);
lean_ctor_set(x_244, 4, x_237);
lean_ctor_set(x_244, 5, x_238);
lean_ctor_set(x_244, 6, x_239);
lean_ctor_set(x_244, 7, x_240);
lean_ctor_set(x_244, 8, x_241);
x_245 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_245, 0, x_217);
lean_ctor_set(x_245, 1, x_218);
lean_ctor_set(x_245, 2, x_219);
lean_ctor_set(x_245, 3, x_220);
lean_ctor_set(x_245, 4, x_221);
lean_ctor_set(x_245, 5, x_222);
lean_ctor_set(x_245, 6, x_223);
lean_ctor_set(x_245, 7, x_224);
lean_ctor_set(x_245, 8, x_226);
lean_ctor_set(x_245, 9, x_227);
lean_ctor_set(x_245, 10, x_228);
lean_ctor_set(x_245, 11, x_229);
lean_ctor_set(x_245, 12, x_230);
lean_ctor_set(x_245, 13, x_231);
lean_ctor_set(x_245, 14, x_244);
lean_ctor_set(x_245, 15, x_232);
lean_ctor_set(x_245, 16, x_233);
lean_ctor_set_uint8(x_245, sizeof(void*)*17, x_225);
x_246 = lean_st_ref_set(x_4, x_245, x_16);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_4);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_312; 
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec_ref(x_246);
x_251 = lean_ctor_get(x_2, 1);
x_252 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_253 = lean_st_ref_get(x_4, x_250);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec_ref(x_253);
x_306 = lean_ctor_get(x_254, 14);
lean_inc_ref(x_306);
lean_dec(x_254);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
lean_dec_ref(x_306);
x_308 = lean_unsigned_to_nat(1u);
x_312 = lean_nat_dec_lt(x_308, x_251);
if (x_312 == 0)
{
x_309 = x_252;
goto block_311;
}
else
{
x_309 = x_312;
goto block_311;
}
block_305:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_257 = lean_st_ref_take(x_4, x_255);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_258, 12);
lean_inc_ref(x_259);
x_260 = lean_ctor_get(x_258, 14);
lean_inc_ref(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
lean_dec_ref(x_257);
x_262 = lean_ctor_get(x_258, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_258, 1);
lean_inc_ref(x_263);
x_264 = lean_ctor_get(x_258, 2);
lean_inc_ref(x_264);
x_265 = lean_ctor_get(x_258, 3);
lean_inc_ref(x_265);
x_266 = lean_ctor_get(x_258, 4);
lean_inc_ref(x_266);
x_267 = lean_ctor_get(x_258, 5);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_258, 6);
lean_inc_ref(x_268);
x_269 = lean_ctor_get(x_258, 7);
lean_inc_ref(x_269);
x_270 = lean_ctor_get_uint8(x_258, sizeof(void*)*17);
x_271 = lean_ctor_get(x_258, 8);
lean_inc(x_271);
x_272 = lean_ctor_get(x_258, 9);
lean_inc_ref(x_272);
x_273 = lean_ctor_get(x_258, 10);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_258, 11);
lean_inc_ref(x_274);
x_275 = lean_ctor_get(x_258, 13);
lean_inc_ref(x_275);
x_276 = lean_ctor_get(x_258, 15);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_258, 16);
lean_inc_ref(x_277);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 lean_ctor_release(x_258, 4);
 lean_ctor_release(x_258, 5);
 lean_ctor_release(x_258, 6);
 lean_ctor_release(x_258, 7);
 lean_ctor_release(x_258, 8);
 lean_ctor_release(x_258, 9);
 lean_ctor_release(x_258, 10);
 lean_ctor_release(x_258, 11);
 lean_ctor_release(x_258, 12);
 lean_ctor_release(x_258, 13);
 lean_ctor_release(x_258, 14);
 lean_ctor_release(x_258, 15);
 lean_ctor_release(x_258, 16);
 x_278 = x_258;
} else {
 lean_dec_ref(x_258);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_259, 0);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_259, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_259, 2);
lean_inc_ref(x_281);
x_282 = lean_ctor_get(x_259, 3);
lean_inc_ref(x_282);
x_283 = lean_ctor_get(x_259, 4);
lean_inc(x_283);
x_284 = lean_ctor_get(x_259, 6);
lean_inc_ref(x_284);
x_285 = lean_ctor_get(x_259, 7);
lean_inc(x_285);
x_286 = lean_ctor_get(x_259, 8);
lean_inc_ref(x_286);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 lean_ctor_release(x_259, 5);
 lean_ctor_release(x_259, 6);
 lean_ctor_release(x_259, 7);
 lean_ctor_release(x_259, 8);
 x_287 = x_259;
} else {
 lean_dec_ref(x_259);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_260, 1);
lean_inc_ref(x_288);
x_289 = lean_ctor_get(x_260, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_260, 3);
lean_inc_ref(x_290);
x_291 = lean_ctor_get(x_260, 4);
lean_inc_ref(x_291);
x_292 = lean_ctor_get(x_260, 5);
lean_inc(x_292);
x_293 = lean_ctor_get(x_260, 6);
lean_inc(x_293);
x_294 = lean_ctor_get(x_260, 7);
lean_inc_ref(x_294);
x_295 = lean_ctor_get(x_260, 8);
lean_inc_ref(x_295);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 lean_ctor_release(x_260, 4);
 lean_ctor_release(x_260, 5);
 lean_ctor_release(x_260, 6);
 lean_ctor_release(x_260, 7);
 lean_ctor_release(x_260, 8);
 x_296 = x_260;
} else {
 lean_dec_ref(x_260);
 x_296 = lean_box(0);
}
x_297 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_287)) {
 x_298 = lean_alloc_ctor(0, 9, 0);
} else {
 x_298 = x_287;
}
lean_ctor_set(x_298, 0, x_279);
lean_ctor_set(x_298, 1, x_280);
lean_ctor_set(x_298, 2, x_281);
lean_ctor_set(x_298, 3, x_282);
lean_ctor_set(x_298, 4, x_283);
lean_ctor_set(x_298, 5, x_297);
lean_ctor_set(x_298, 6, x_284);
lean_ctor_set(x_298, 7, x_285);
lean_ctor_set(x_298, 8, x_286);
if (lean_is_scalar(x_296)) {
 x_299 = lean_alloc_ctor(0, 9, 0);
} else {
 x_299 = x_296;
}
lean_ctor_set(x_299, 0, x_256);
lean_ctor_set(x_299, 1, x_288);
lean_ctor_set(x_299, 2, x_289);
lean_ctor_set(x_299, 3, x_290);
lean_ctor_set(x_299, 4, x_291);
lean_ctor_set(x_299, 5, x_292);
lean_ctor_set(x_299, 6, x_293);
lean_ctor_set(x_299, 7, x_294);
lean_ctor_set(x_299, 8, x_295);
if (lean_is_scalar(x_278)) {
 x_300 = lean_alloc_ctor(0, 17, 1);
} else {
 x_300 = x_278;
}
lean_ctor_set(x_300, 0, x_262);
lean_ctor_set(x_300, 1, x_263);
lean_ctor_set(x_300, 2, x_264);
lean_ctor_set(x_300, 3, x_265);
lean_ctor_set(x_300, 4, x_266);
lean_ctor_set(x_300, 5, x_267);
lean_ctor_set(x_300, 6, x_268);
lean_ctor_set(x_300, 7, x_269);
lean_ctor_set(x_300, 8, x_271);
lean_ctor_set(x_300, 9, x_272);
lean_ctor_set(x_300, 10, x_273);
lean_ctor_set(x_300, 11, x_274);
lean_ctor_set(x_300, 12, x_298);
lean_ctor_set(x_300, 13, x_275);
lean_ctor_set(x_300, 14, x_299);
lean_ctor_set(x_300, 15, x_276);
lean_ctor_set(x_300, 16, x_277);
lean_ctor_set_uint8(x_300, sizeof(void*)*17, x_270);
x_301 = lean_st_ref_set(x_4, x_300, x_261);
lean_dec(x_4);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_2);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
block_311:
{
if (x_309 == 0)
{
x_256 = x_307;
goto block_305;
}
else
{
lean_object* x_310; 
x_310 = lean_nat_add(x_307, x_308);
lean_dec(x_307);
x_256 = x_310;
goto block_305;
}
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; uint8_t x_426; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_313 = lean_ctor_get(x_1, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_1, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_315 = x_1;
} else {
 lean_dec_ref(x_1);
 x_315 = lean_box(0);
}
x_476 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7;
x_477 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__8___redArg(x_476, x_10, x_12);
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_unbox(x_478);
lean_dec(x_478);
if (x_479 == 0)
{
lean_object* x_480; 
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
lean_dec_ref(x_477);
x_437 = x_4;
x_438 = x_5;
x_439 = x_6;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_480;
goto block_475;
}
else
{
uint8_t x_481; 
x_481 = !lean_is_exclusive(x_477);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_477, 1);
x_483 = lean_ctor_get(x_477, 0);
lean_dec(x_483);
x_484 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_482);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec_ref(x_484);
x_486 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
x_487 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_313);
x_488 = l_Lean_MessageData_ofExpr(x_487);
lean_ctor_set_tag(x_477, 7);
lean_ctor_set(x_477, 1, x_488);
lean_ctor_set(x_477, 0, x_486);
x_489 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_476, x_477, x_8, x_9, x_10, x_11, x_485);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec_ref(x_489);
x_437 = x_4;
x_438 = x_5;
x_439 = x_6;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_490;
goto block_475;
}
else
{
uint8_t x_491; 
lean_free_object(x_477);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_491 = !lean_is_exclusive(x_484);
if (x_491 == 0)
{
return x_484;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_484, 0);
x_493 = lean_ctor_get(x_484, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_484);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
else
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_477, 1);
lean_inc(x_495);
lean_dec(x_477);
x_496 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec_ref(x_496);
x_498 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
x_499 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_313);
x_500 = l_Lean_MessageData_ofExpr(x_499);
x_501 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_500);
x_502 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg(x_476, x_501, x_8, x_9, x_10, x_11, x_497);
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
lean_dec_ref(x_502);
x_437 = x_4;
x_438 = x_5;
x_439 = x_6;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_503;
goto block_475;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_504 = lean_ctor_get(x_496, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_496, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_506 = x_496;
} else {
 lean_dec_ref(x_496);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
}
block_327:
{
lean_object* x_325; 
if (lean_is_scalar(x_315)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_315;
}
lean_ctor_set(x_325, 0, x_313);
lean_ctor_set(x_325, 1, x_3);
x_1 = x_314;
x_3 = x_325;
x_4 = x_321;
x_5 = x_320;
x_6 = x_322;
x_7 = x_323;
x_8 = x_319;
x_9 = x_318;
x_10 = x_316;
x_11 = x_317;
x_12 = x_324;
goto _start;
}
block_344:
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(x_341, 0, x_313);
lean_ctor_set(x_341, 1, x_329);
lean_ctor_set_uint8(x_341, sizeof(void*)*2, x_335);
lean_ctor_set_uint8(x_341, sizeof(void*)*2 + 1, x_338);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_337);
lean_ctor_set(x_342, 1, x_3);
x_1 = x_314;
x_2 = x_341;
x_3 = x_342;
x_4 = x_334;
x_5 = x_333;
x_6 = x_336;
x_7 = x_339;
x_8 = x_332;
x_9 = x_331;
x_10 = x_328;
x_11 = x_330;
x_12 = x_340;
goto _start;
}
block_377:
{
lean_object* x_359; lean_object* x_360; 
x_359 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_313);
x_360 = l_Lean_Meta_Grind_getGeneration___redArg(x_359, x_347, x_357);
lean_dec_ref(x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec_ref(x_360);
x_363 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_352);
x_364 = l_Lean_Meta_Grind_getGeneration___redArg(x_363, x_347, x_362);
lean_dec_ref(x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec_ref(x_364);
x_367 = lean_nat_dec_lt(x_361, x_365);
lean_dec(x_365);
lean_dec(x_361);
if (x_367 == 0)
{
uint8_t x_368; 
x_368 = lean_nat_dec_lt(x_353, x_350);
lean_dec(x_350);
if (x_368 == 0)
{
lean_dec(x_353);
lean_dec_ref(x_352);
x_316 = x_345;
x_317 = x_346;
x_318 = x_348;
x_319 = x_349;
x_320 = x_354;
x_321 = x_347;
x_322 = x_356;
x_323 = x_358;
x_324 = x_366;
goto block_327;
}
else
{
lean_dec(x_315);
lean_dec(x_2);
x_328 = x_345;
x_329 = x_353;
x_330 = x_346;
x_331 = x_348;
x_332 = x_349;
x_333 = x_354;
x_334 = x_347;
x_335 = x_355;
x_336 = x_356;
x_337 = x_352;
x_338 = x_351;
x_339 = x_358;
x_340 = x_366;
goto block_344;
}
}
else
{
lean_dec(x_350);
lean_dec(x_315);
lean_dec(x_2);
x_328 = x_345;
x_329 = x_353;
x_330 = x_346;
x_331 = x_348;
x_332 = x_349;
x_333 = x_354;
x_334 = x_347;
x_335 = x_355;
x_336 = x_356;
x_337 = x_352;
x_338 = x_351;
x_339 = x_358;
x_340 = x_366;
goto block_344;
}
}
else
{
uint8_t x_369; 
lean_dec(x_361);
lean_dec(x_358);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_350);
lean_dec_ref(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_3);
lean_dec(x_2);
x_369 = !lean_is_exclusive(x_364);
if (x_369 == 0)
{
return x_364;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_364, 0);
x_371 = lean_ctor_get(x_364, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_364);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
uint8_t x_373; 
lean_dec(x_358);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_350);
lean_dec_ref(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec_ref(x_345);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_3);
lean_dec(x_2);
x_373 = !lean_is_exclusive(x_360);
if (x_373 == 0)
{
return x_360;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_360, 0);
x_375 = lean_ctor_get(x_360, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_360);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
block_395:
{
if (x_392 == 0)
{
x_345 = x_378;
x_346 = x_379;
x_347 = x_380;
x_348 = x_381;
x_349 = x_382;
x_350 = x_383;
x_351 = x_384;
x_352 = x_385;
x_353 = x_386;
x_354 = x_387;
x_355 = x_388;
x_356 = x_389;
x_357 = x_390;
x_358 = x_391;
goto block_377;
}
else
{
lean_object* x_393; uint8_t x_394; 
x_393 = lean_unsigned_to_nat(1u);
x_394 = lean_nat_dec_lt(x_393, x_383);
if (x_394 == 0)
{
x_345 = x_378;
x_346 = x_379;
x_347 = x_380;
x_348 = x_381;
x_349 = x_382;
x_350 = x_383;
x_351 = x_384;
x_352 = x_385;
x_353 = x_386;
x_354 = x_387;
x_355 = x_388;
x_356 = x_389;
x_357 = x_390;
x_358 = x_391;
goto block_377;
}
else
{
lean_dec(x_383);
lean_dec(x_315);
lean_dec(x_2);
x_328 = x_378;
x_329 = x_386;
x_330 = x_379;
x_331 = x_381;
x_332 = x_382;
x_333 = x_387;
x_334 = x_380;
x_335 = x_388;
x_336 = x_389;
x_337 = x_385;
x_338 = x_384;
x_339 = x_391;
x_340 = x_390;
goto block_344;
}
}
}
block_413:
{
lean_object* x_411; uint8_t x_412; 
x_411 = lean_unsigned_to_nat(1u);
x_412 = lean_nat_dec_eq(x_404, x_411);
if (x_412 == 0)
{
x_378 = x_396;
x_379 = x_397;
x_380 = x_398;
x_381 = x_399;
x_382 = x_400;
x_383 = x_401;
x_384 = x_402;
x_385 = x_403;
x_386 = x_404;
x_387 = x_405;
x_388 = x_406;
x_389 = x_407;
x_390 = x_408;
x_391 = x_409;
x_392 = x_412;
goto block_395;
}
else
{
if (x_406 == 0)
{
x_378 = x_396;
x_379 = x_397;
x_380 = x_398;
x_381 = x_399;
x_382 = x_400;
x_383 = x_401;
x_384 = x_402;
x_385 = x_403;
x_386 = x_404;
x_387 = x_405;
x_388 = x_406;
x_389 = x_407;
x_390 = x_408;
x_391 = x_409;
x_392 = x_412;
goto block_395;
}
else
{
x_378 = x_396;
x_379 = x_397;
x_380 = x_398;
x_381 = x_399;
x_382 = x_400;
x_383 = x_401;
x_384 = x_402;
x_385 = x_403;
x_386 = x_404;
x_387 = x_405;
x_388 = x_406;
x_389 = x_407;
x_390 = x_408;
x_391 = x_409;
x_392 = x_410;
goto block_395;
}
}
}
block_436:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_427; 
lean_dec(x_315);
x_427 = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(x_427, 0, x_313);
lean_ctor_set(x_427, 1, x_415);
lean_ctor_set_uint8(x_427, sizeof(void*)*2, x_421);
lean_ctor_set_uint8(x_427, sizeof(void*)*2 + 1, x_424);
x_1 = x_314;
x_2 = x_427;
x_4 = x_420;
x_5 = x_419;
x_6 = x_422;
x_7 = x_425;
x_8 = x_418;
x_9 = x_417;
x_10 = x_414;
x_11 = x_416;
x_12 = x_423;
goto _start;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
if (x_429 == 0)
{
if (x_424 == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_2, 0);
x_431 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_430);
lean_inc(x_431);
x_396 = x_414;
x_397 = x_416;
x_398 = x_420;
x_399 = x_417;
x_400 = x_418;
x_401 = x_431;
x_402 = x_424;
x_403 = x_430;
x_404 = x_415;
x_405 = x_419;
x_406 = x_421;
x_407 = x_422;
x_408 = x_423;
x_409 = x_425;
x_410 = x_424;
goto block_413;
}
else
{
lean_dec(x_415);
x_316 = x_414;
x_317 = x_416;
x_318 = x_417;
x_319 = x_418;
x_320 = x_419;
x_321 = x_420;
x_322 = x_422;
x_323 = x_425;
x_324 = x_423;
goto block_327;
}
}
else
{
if (x_424 == 0)
{
lean_object* x_432; 
lean_dec(x_315);
x_432 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_432);
lean_dec_ref(x_2);
x_328 = x_414;
x_329 = x_415;
x_330 = x_416;
x_331 = x_417;
x_332 = x_418;
x_333 = x_419;
x_334 = x_420;
x_335 = x_421;
x_336 = x_422;
x_337 = x_432;
x_338 = x_424;
x_339 = x_425;
x_340 = x_423;
goto block_344;
}
else
{
if (x_426 == 0)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_2, 0);
x_434 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_433);
lean_inc(x_434);
x_396 = x_414;
x_397 = x_416;
x_398 = x_420;
x_399 = x_417;
x_400 = x_418;
x_401 = x_434;
x_402 = x_424;
x_403 = x_433;
x_404 = x_415;
x_405 = x_419;
x_406 = x_421;
x_407 = x_422;
x_408 = x_423;
x_409 = x_425;
x_410 = x_426;
goto block_413;
}
else
{
lean_object* x_435; 
lean_dec(x_315);
x_435 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_435);
lean_dec_ref(x_2);
x_328 = x_414;
x_329 = x_415;
x_330 = x_416;
x_331 = x_417;
x_332 = x_418;
x_333 = x_419;
x_334 = x_420;
x_335 = x_421;
x_336 = x_422;
x_337 = x_435;
x_338 = x_424;
x_339 = x_425;
x_340 = x_423;
goto block_344;
}
}
}
}
}
block_475:
{
lean_object* x_446; 
lean_inc(x_444);
lean_inc_ref(x_443);
lean_inc(x_442);
lean_inc_ref(x_441);
lean_inc(x_440);
lean_inc_ref(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_313);
x_446 = l_Lean_Meta_Grind_checkSplitStatus(x_313, x_437, x_438, x_439, x_440, x_441, x_442, x_443, x_444, x_445);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
switch (lean_obj_tag(x_447)) {
case 0:
{
lean_object* x_448; 
lean_dec(x_315);
lean_dec(x_313);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec_ref(x_446);
x_1 = x_314;
x_4 = x_437;
x_5 = x_438;
x_6 = x_439;
x_7 = x_440;
x_8 = x_441;
x_9 = x_442;
x_10 = x_443;
x_11 = x_444;
x_12 = x_448;
goto _start;
}
case 1:
{
lean_object* x_450; lean_object* x_451; 
lean_dec(x_315);
x_450 = lean_ctor_get(x_446, 1);
lean_inc(x_450);
lean_dec_ref(x_446);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_313);
lean_ctor_set(x_451, 1, x_3);
x_1 = x_314;
x_3 = x_451;
x_4 = x_437;
x_5 = x_438;
x_6 = x_439;
x_7 = x_440;
x_8 = x_441;
x_9 = x_442;
x_10 = x_443;
x_11 = x_444;
x_12 = x_450;
goto _start;
}
default: 
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_456; lean_object* x_457; 
x_453 = lean_ctor_get(x_446, 1);
lean_inc(x_453);
lean_dec_ref(x_446);
x_454 = lean_ctor_get(x_447, 0);
lean_inc(x_454);
x_455 = lean_ctor_get_uint8(x_447, sizeof(void*)*1);
x_456 = lean_ctor_get_uint8(x_447, sizeof(void*)*1 + 1);
lean_dec_ref(x_447);
x_457 = l_Lean_Meta_Grind_cheapCasesOnly___redArg(x_439, x_453);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; uint8_t x_459; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_unbox(x_458);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; 
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
lean_dec_ref(x_457);
x_461 = lean_unbox(x_458);
lean_dec(x_458);
x_414 = x_443;
x_415 = x_454;
x_416 = x_444;
x_417 = x_442;
x_418 = x_441;
x_419 = x_438;
x_420 = x_437;
x_421 = x_455;
x_422 = x_439;
x_423 = x_460;
x_424 = x_456;
x_425 = x_440;
x_426 = x_461;
goto block_436;
}
else
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; 
lean_dec(x_458);
x_462 = lean_ctor_get(x_457, 1);
lean_inc(x_462);
lean_dec_ref(x_457);
x_463 = lean_unsigned_to_nat(1u);
x_464 = lean_nat_dec_lt(x_463, x_454);
if (x_464 == 0)
{
x_414 = x_443;
x_415 = x_454;
x_416 = x_444;
x_417 = x_442;
x_418 = x_441;
x_419 = x_438;
x_420 = x_437;
x_421 = x_455;
x_422 = x_439;
x_423 = x_462;
x_424 = x_456;
x_425 = x_440;
x_426 = x_464;
goto block_436;
}
else
{
lean_object* x_465; 
lean_dec(x_454);
lean_dec(x_315);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_313);
lean_ctor_set(x_465, 1, x_3);
x_1 = x_314;
x_3 = x_465;
x_4 = x_437;
x_5 = x_438;
x_6 = x_439;
x_7 = x_440;
x_8 = x_441;
x_9 = x_442;
x_10 = x_443;
x_11 = x_444;
x_12 = x_462;
goto _start;
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_454);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_3);
lean_dec(x_2);
x_467 = !lean_is_exclusive(x_457);
if (x_467 == 0)
{
return x_457;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_457, 0);
x_469 = lean_ctor_get(x_457, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_457);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec_ref(x_439);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_3);
lean_dec(x_2);
x_471 = !lean_is_exclusive(x_446);
if (x_471 == 0)
{
return x_446;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_446, 0);
x_473 = lean_ctor_get(x_446, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_446);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_isInconsistent___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(x_1, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_st_ref_get(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 14);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(x_22, x_23, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_10, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_10, 0, x_38);
return x_10;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
x_3 = l_Lean_mkConst(x_2, x_1);
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
x_3 = l_Lean_mkConst(x_2, x_1);
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
x_3 = l_Lean_mkConst(x_2, x_1);
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
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_49; 
lean_inc_ref(x_1);
x_49 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
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
lean_dec_ref(x_64);
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
lean_inc_ref(x_66);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_68 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
x_69 = l_Lean_Expr_isConstOf(x_67, x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isApp(x_67);
if (x_70 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_66);
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
lean_inc_ref(x_71);
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_73 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_74 = l_Lean_Expr_isConstOf(x_72, x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_isApp(x_72);
if (x_75 == 0)
{
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_66);
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
x_77 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
x_78 = l_Lean_Expr_isConstOf(x_76, x_77);
lean_dec_ref(x_76);
if (x_78 == 0)
{
lean_dec_ref(x_71);
lean_dec_ref(x_66);
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
lean_inc_ref(x_1);
x_79 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec_ref(x_71);
lean_dec_ref(x_66);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_81);
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
lean_dec_ref(x_71);
lean_dec_ref(x_66);
return x_85;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
lean_dec_ref(x_81);
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
lean_dec_ref(x_71);
lean_dec_ref(x_66);
return x_96;
}
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_71);
lean_dec_ref(x_66);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_72);
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
lean_dec_ref(x_71);
lean_dec_ref(x_66);
return x_110;
}
}
}
}
else
{
lean_object* x_120; 
lean_dec_ref(x_67);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
x_11 = x_60;
x_12 = x_57;
x_13 = x_54;
x_14 = x_59;
x_15 = x_52;
x_16 = x_58;
x_17 = x_53;
x_18 = x_56;
x_19 = x_55;
x_20 = x_62;
goto block_48;
}
else
{
x_11 = x_60;
x_12 = x_57;
x_13 = x_54;
x_14 = x_59;
x_15 = x_52;
x_16 = x_58;
x_17 = x_53;
x_18 = x_56;
x_19 = x_55;
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
lean_dec_ref(x_134);
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
lean_inc_ref(x_136);
x_137 = l_Lean_Expr_appFnCleanup___redArg(x_134);
x_138 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
x_139 = l_Lean_Expr_isConstOf(x_137, x_138);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = l_Lean_Expr_isApp(x_137);
if (x_140 == 0)
{
lean_dec_ref(x_137);
lean_dec_ref(x_136);
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
lean_inc_ref(x_141);
x_142 = l_Lean_Expr_appFnCleanup___redArg(x_137);
x_143 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_144 = l_Lean_Expr_isConstOf(x_142, x_143);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Lean_Expr_isApp(x_142);
if (x_145 == 0)
{
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_136);
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
x_147 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
x_148 = l_Lean_Expr_isConstOf(x_146, x_147);
lean_dec_ref(x_146);
if (x_148 == 0)
{
lean_dec_ref(x_141);
lean_dec_ref(x_136);
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
lean_inc_ref(x_1);
x_149 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_141);
lean_dec_ref(x_136);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_152);
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
lean_dec_ref(x_141);
lean_dec_ref(x_136);
return x_156;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_152, 1);
lean_inc(x_163);
lean_dec_ref(x_152);
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
lean_dec_ref(x_141);
lean_dec_ref(x_136);
return x_164;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_141);
lean_dec_ref(x_136);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_142);
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
lean_dec_ref(x_141);
lean_dec_ref(x_136);
return x_175;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec_ref(x_137);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
x_11 = x_130;
x_12 = x_127;
x_13 = x_124;
x_14 = x_129;
x_15 = x_122;
x_16 = x_128;
x_17 = x_123;
x_18 = x_126;
x_19 = x_125;
x_20 = x_132;
goto block_48;
}
else
{
x_11 = x_130;
x_12 = x_127;
x_13 = x_124;
x_14 = x_129;
x_15 = x_122;
x_16 = x_128;
x_17 = x_123;
x_18 = x_126;
x_19 = x_125;
x_20 = x_131;
goto block_48;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_49;
}
block_48:
{
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc_ref(x_1);
x_21 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_17, x_19, x_14, x_11, x_15);
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
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
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
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_29 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_17, x_13, x_19, x_18, x_12, x_16, x_14, x_11, x_28);
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
lean_dec_ref(x_1);
return x_29;
}
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_1);
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
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Lean_Expr_getAppNumArgs(x_1);
x_43 = lean_nat_sub(x_42, x_41);
lean_dec(x_42);
x_44 = lean_nat_sub(x_43, x_41);
lean_dec(x_43);
x_45 = l_Lean_Expr_getRevArg_x21(x_1, x_44);
lean_dec_ref(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_15);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = l_Lean_Meta_Grind_cases(x_1, x_2, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_16 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_19 = l_Lean_Meta_whnfD(x_17, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Expr_getAppFn(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 0;
x_25 = l_Lean_Meta_Grind_saveCases___redArg(x_23, x_24, x_3, x_4, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Meta_Grind_cases(x_1, x_2, x_5, x_6, x_7, x_8, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec_ref(x_22);
x_32 = l_Lean_Meta_Grind_cases(x_1, x_2, x_5, x_6, x_7, x_8, x_21);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_array_to_list(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 14);
lean_inc_ref(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get(x_1, 5);
x_18 = lean_ctor_get(x_1, 6);
x_19 = lean_ctor_get(x_1, 7);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*17);
x_21 = lean_ctor_get(x_1, 8);
x_22 = lean_ctor_get(x_1, 9);
x_23 = lean_ctor_get(x_1, 10);
x_24 = lean_ctor_get(x_1, 11);
x_25 = lean_ctor_get(x_1, 12);
x_26 = lean_ctor_get(x_1, 13);
x_27 = lean_ctor_get(x_1, 15);
x_28 = lean_ctor_get(x_1, 16);
x_29 = lean_ctor_get(x_8, 5);
x_30 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_3);
lean_ctor_set(x_31, 3, x_4);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_31);
lean_ctor_set(x_8, 5, x_5);
lean_inc_ref(x_28);
lean_inc_ref(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_25);
lean_inc_ref(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
lean_inc_ref(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_32 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_14);
lean_ctor_set(x_32, 3, x_15);
lean_ctor_set(x_32, 4, x_16);
lean_ctor_set(x_32, 5, x_17);
lean_ctor_set(x_32, 6, x_18);
lean_ctor_set(x_32, 7, x_19);
lean_ctor_set(x_32, 8, x_21);
lean_ctor_set(x_32, 9, x_22);
lean_ctor_set(x_32, 10, x_23);
lean_ctor_set(x_32, 11, x_24);
lean_ctor_set(x_32, 12, x_25);
lean_ctor_set(x_32, 13, x_26);
lean_ctor_set(x_32, 14, x_8);
lean_ctor_set(x_32, 15, x_27);
lean_ctor_set(x_32, 16, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*17, x_20);
x_33 = lean_array_push(x_6, x_32);
x_5 = x_12;
x_6 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
x_39 = lean_ctor_get(x_1, 3);
x_40 = lean_ctor_get(x_1, 4);
x_41 = lean_ctor_get(x_1, 5);
x_42 = lean_ctor_get(x_1, 6);
x_43 = lean_ctor_get(x_1, 7);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*17);
x_45 = lean_ctor_get(x_1, 8);
x_46 = lean_ctor_get(x_1, 9);
x_47 = lean_ctor_get(x_1, 10);
x_48 = lean_ctor_get(x_1, 11);
x_49 = lean_ctor_get(x_1, 12);
x_50 = lean_ctor_get(x_1, 13);
x_51 = lean_ctor_get(x_1, 15);
x_52 = lean_ctor_get(x_1, 16);
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
x_55 = lean_ctor_get(x_8, 2);
x_56 = lean_ctor_get(x_8, 3);
x_57 = lean_ctor_get(x_8, 4);
x_58 = lean_ctor_get(x_8, 5);
x_59 = lean_ctor_get(x_8, 6);
x_60 = lean_ctor_get(x_8, 7);
x_61 = lean_ctor_get(x_8, 8);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_62 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_3);
lean_ctor_set(x_63, 3, x_4);
lean_ctor_set(x_5, 1, x_58);
lean_ctor_set(x_5, 0, x_63);
x_64 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_55);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_5);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_ctor_set(x_64, 8, x_61);
lean_inc_ref(x_52);
lean_inc_ref(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_43);
lean_inc_ref(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_37);
x_65 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_65, 0, x_35);
lean_ctor_set(x_65, 1, x_37);
lean_ctor_set(x_65, 2, x_38);
lean_ctor_set(x_65, 3, x_39);
lean_ctor_set(x_65, 4, x_40);
lean_ctor_set(x_65, 5, x_41);
lean_ctor_set(x_65, 6, x_42);
lean_ctor_set(x_65, 7, x_43);
lean_ctor_set(x_65, 8, x_45);
lean_ctor_set(x_65, 9, x_46);
lean_ctor_set(x_65, 10, x_47);
lean_ctor_set(x_65, 11, x_48);
lean_ctor_set(x_65, 12, x_49);
lean_ctor_set(x_65, 13, x_50);
lean_ctor_set(x_65, 14, x_64);
lean_ctor_set(x_65, 15, x_51);
lean_ctor_set(x_65, 16, x_52);
lean_ctor_set_uint8(x_65, sizeof(void*)*17, x_44);
x_66 = lean_array_push(x_6, x_65);
x_5 = x_36;
x_6 = x_66;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_5);
x_70 = lean_ctor_get(x_1, 1);
x_71 = lean_ctor_get(x_1, 2);
x_72 = lean_ctor_get(x_1, 3);
x_73 = lean_ctor_get(x_1, 4);
x_74 = lean_ctor_get(x_1, 5);
x_75 = lean_ctor_get(x_1, 6);
x_76 = lean_ctor_get(x_1, 7);
x_77 = lean_ctor_get_uint8(x_1, sizeof(void*)*17);
x_78 = lean_ctor_get(x_1, 8);
x_79 = lean_ctor_get(x_1, 9);
x_80 = lean_ctor_get(x_1, 10);
x_81 = lean_ctor_get(x_1, 11);
x_82 = lean_ctor_get(x_1, 12);
x_83 = lean_ctor_get(x_1, 13);
x_84 = lean_ctor_get(x_1, 15);
x_85 = lean_ctor_get(x_1, 16);
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_8, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_8, 5);
lean_inc(x_91);
x_92 = lean_ctor_get(x_8, 6);
lean_inc(x_92);
x_93 = lean_ctor_get(x_8, 7);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_8, 8);
lean_inc_ref(x_94);
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
 x_95 = x_8;
} else {
 lean_dec_ref(x_8);
 x_95 = lean_box(0);
}
x_96 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_3);
lean_ctor_set(x_97, 3, x_4);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_91);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 9, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_87);
lean_ctor_set(x_99, 2, x_88);
lean_ctor_set(x_99, 3, x_89);
lean_ctor_set(x_99, 4, x_90);
lean_ctor_set(x_99, 5, x_98);
lean_ctor_set(x_99, 6, x_92);
lean_ctor_set(x_99, 7, x_93);
lean_ctor_set(x_99, 8, x_94);
lean_inc_ref(x_85);
lean_inc_ref(x_84);
lean_inc_ref(x_83);
lean_inc_ref(x_82);
lean_inc_ref(x_81);
lean_inc_ref(x_80);
lean_inc_ref(x_79);
lean_inc(x_78);
lean_inc_ref(x_76);
lean_inc_ref(x_75);
lean_inc_ref(x_74);
lean_inc_ref(x_73);
lean_inc_ref(x_72);
lean_inc_ref(x_71);
lean_inc_ref(x_70);
x_100 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_100, 0, x_68);
lean_ctor_set(x_100, 1, x_70);
lean_ctor_set(x_100, 2, x_71);
lean_ctor_set(x_100, 3, x_72);
lean_ctor_set(x_100, 4, x_73);
lean_ctor_set(x_100, 5, x_74);
lean_ctor_set(x_100, 6, x_75);
lean_ctor_set(x_100, 7, x_76);
lean_ctor_set(x_100, 8, x_78);
lean_ctor_set(x_100, 9, x_79);
lean_ctor_set(x_100, 10, x_80);
lean_ctor_set(x_100, 11, x_81);
lean_ctor_set(x_100, 12, x_82);
lean_ctor_set(x_100, 13, x_83);
lean_ctor_set(x_100, 14, x_99);
lean_ctor_set(x_100, 15, x_84);
lean_ctor_set(x_100, 16, x_85);
lean_ctor_set_uint8(x_100, sizeof(void*)*17, x_77);
x_101 = lean_array_push(x_6, x_100);
x_5 = x_69;
x_6 = x_101;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_15, x_30);
lean_dec(x_15);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___lam__0___boxed), 9, 0);
lean_inc(x_2);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_st_ref_take(x_2, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_21);
x_27 = lean_st_ref_set(x_2, x_23, x_24);
lean_dec(x_2);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_isMatcherAppCore(x_20, x_1);
x_30 = lean_box(x_29);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_st_ref_set(x_2, x_32, x_24);
lean_dec(x_2);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_isMatcherAppCore(x_20, x_1);
x_36 = lean_box(x_35);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_36);
return x_16;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_st_ref_take(x_2, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_st_ref_set(x_2, x_46, x_43);
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_isMatcherAppCore(x_39, x_1);
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_16);
if (x_52 == 0)
{
return x_16;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_16, 0);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_16);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_7, 13);
x_19 = lean_st_ref_get(x_16, x_17);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_18);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
lean_inc_ref(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ctor_get(x_7, 13);
x_29 = lean_st_ref_get(x_26, x_27);
lean_dec(x_26);
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
lean_inc_ref(x_28);
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
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
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_18);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ctor_get(x_7, 2);
x_29 = lean_st_ref_get(x_26, x_27);
lean_dec(x_26);
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
lean_inc(x_28);
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__0___boxed), 9, 0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
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
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_st_ref_set(x_2, x_22, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed), 9, 0);
lean_inc(x_2);
x_33 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_31, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_st_ref_take(x_2, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
lean_ctor_set(x_40, 0, x_38);
x_44 = lean_st_ref_set(x_2, x_40, x_41);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_checkTraceOption(x_19, x_37, x_1);
lean_dec(x_37);
lean_dec(x_19);
x_47 = lean_box(x_46);
lean_ctor_set(x_33, 1, x_45);
lean_ctor_set(x_33, 0, x_47);
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_st_ref_set(x_2, x_49, x_41);
lean_dec(x_2);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_checkTraceOption(x_19, x_37, x_1);
lean_dec(x_37);
lean_dec(x_19);
x_53 = lean_box(x_52);
lean_ctor_set(x_33, 1, x_51);
lean_ctor_set(x_33, 0, x_53);
return x_33;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_st_ref_take(x_2, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_st_ref_set(x_2, x_63, x_60);
lean_dec(x_2);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_checkTraceOption(x_19, x_56, x_1);
lean_dec(x_56);
lean_dec(x_19);
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_33);
if (x_69 == 0)
{
return x_33;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_33, 0);
x_71 = lean_ctor_get(x_33, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_33);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_28);
if (x_73 == 0)
{
return x_28;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_28, 0);
x_75 = lean_ctor_get(x_28, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_28);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
lean_dec(x_22);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_20);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_st_ref_set(x_2, x_78, x_23);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed), 9, 0);
lean_inc(x_2);
x_86 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_84, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_st_ref_take(x_2, x_88);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_st_ref_set(x_2, x_97, x_94);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lean_checkTraceOption(x_19, x_90, x_1);
lean_dec(x_90);
lean_dec(x_19);
x_101 = lean_box(x_100);
if (lean_is_scalar(x_89)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_89;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_86, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_86, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_105 = x_86;
} else {
 lean_dec_ref(x_86);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_ctor_get(x_81, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_109 = x_81;
} else {
 lean_dec_ref(x_81);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_16);
if (x_111 == 0)
{
return x_16;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_16, 0);
x_113 = lean_ctor_get(x_16, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_16);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_11);
if (x_115 == 0)
{
return x_11;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_11, 0);
x_117 = lean_ctor_get(x_11, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_11);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_1, x_6, x_7, x_8, x_9, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_st_ref_get(x_16, x_30);
lean_dec(x_16);
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
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_take(x_11, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 4);
lean_inc_ref(x_22);
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
lean_object* x_29; double x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_31 = 0;
x_32 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_33 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_float(x_33, sizeof(void*)*2, x_30);
lean_ctor_set_float(x_33, sizeof(void*)*2 + 8, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 16, x_31);
x_34 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_20, 1, x_35);
lean_ctor_set(x_20, 0, x_3);
x_36 = l_Lean_PersistentArray_push___redArg(x_29, x_20);
lean_ctor_set(x_22, 0, x_36);
x_37 = lean_st_ref_set(x_11, x_21, x_24);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_st_ref_get(x_18, x_39);
lean_dec(x_18);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_box(0);
lean_ctor_set(x_41, 1, x_43);
lean_ctor_set(x_41, 0, x_45);
lean_ctor_set(x_37, 1, x_44);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_37, 1, x_47);
lean_ctor_set(x_37, 0, x_49);
return x_37;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_dec(x_37);
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
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
else
{
uint64_t x_58; lean_object* x_59; double x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_58 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
lean_dec(x_22);
x_60 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_61 = 0;
x_62 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_63 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_float(x_63, sizeof(void*)*2, x_60);
lean_ctor_set_float(x_63, sizeof(void*)*2 + 8, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*2 + 16, x_61);
x_64 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_65 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_2);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_20, 1, x_65);
lean_ctor_set(x_20, 0, x_3);
x_66 = l_Lean_PersistentArray_push___redArg(x_59, x_20);
x_67 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set_uint64(x_67, sizeof(void*)*1, x_58);
lean_ctor_set(x_21, 4, x_67);
x_68 = lean_st_ref_set(x_11, x_21, x_24);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_st_ref_get(x_18, x_69);
lean_dec(x_18);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_78 = lean_ctor_get(x_21, 0);
x_79 = lean_ctor_get(x_21, 1);
x_80 = lean_ctor_get(x_21, 2);
x_81 = lean_ctor_get(x_21, 3);
x_82 = lean_ctor_get(x_21, 5);
x_83 = lean_ctor_get(x_21, 6);
x_84 = lean_ctor_get(x_21, 7);
x_85 = lean_ctor_get(x_21, 8);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_21);
x_86 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_87 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_88 = x_22;
} else {
 lean_dec_ref(x_22);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_20, 1, x_94);
lean_ctor_set(x_20, 0, x_3);
x_95 = l_Lean_PersistentArray_push___redArg(x_87, x_20);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(0, 1, 8);
} else {
 x_96 = x_88;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set_uint64(x_96, sizeof(void*)*1, x_86);
x_97 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_97, 0, x_78);
lean_ctor_set(x_97, 1, x_79);
lean_ctor_set(x_97, 2, x_80);
lean_ctor_set(x_97, 3, x_81);
lean_ctor_set(x_97, 4, x_96);
lean_ctor_set(x_97, 5, x_82);
lean_ctor_set(x_97, 6, x_83);
lean_ctor_set(x_97, 7, x_84);
lean_ctor_set(x_97, 8, x_85);
x_98 = lean_st_ref_set(x_11, x_97, x_24);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_st_ref_get(x_18, x_99);
lean_dec(x_18);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; double x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_108 = lean_ctor_get(x_20, 1);
lean_inc(x_108);
lean_dec(x_20);
x_109 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_21, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_21, 3);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_21, 5);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_21, 6);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_21, 7);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_21, 8);
lean_inc_ref(x_116);
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
 x_117 = x_21;
} else {
 lean_dec_ref(x_21);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_119 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_119);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_120 = x_22;
} else {
 lean_dec_ref(x_22);
 x_120 = lean_box(0);
}
x_121 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0;
x_122 = 0;
x_123 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1;
x_124 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set_float(x_124, sizeof(void*)*2, x_121);
lean_ctor_set_float(x_124, sizeof(void*)*2 + 8, x_121);
lean_ctor_set_uint8(x_124, sizeof(void*)*2 + 16, x_122);
x_125 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2;
x_126 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_2);
lean_ctor_set(x_126, 2, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_3);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_PersistentArray_push___redArg(x_119, x_127);
if (lean_is_scalar(x_120)) {
 x_129 = lean_alloc_ctor(0, 1, 8);
} else {
 x_129 = x_120;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set_uint64(x_129, sizeof(void*)*1, x_118);
if (lean_is_scalar(x_117)) {
 x_130 = lean_alloc_ctor(0, 9, 0);
} else {
 x_130 = x_117;
}
lean_ctor_set(x_130, 0, x_109);
lean_ctor_set(x_130, 1, x_110);
lean_ctor_set(x_130, 2, x_111);
lean_ctor_set(x_130, 3, x_112);
lean_ctor_set(x_130, 4, x_129);
lean_ctor_set(x_130, 5, x_113);
lean_ctor_set(x_130, 6, x_114);
lean_ctor_set(x_130, 7, x_115);
lean_ctor_set(x_130, 8, x_116);
x_131 = lean_st_ref_set(x_11, x_130, x_108);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_st_ref_get(x_18, x_132);
lean_dec(x_18);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_135);
if (lean_is_scalar(x_133)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_133;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__0___boxed), 10, 1);
lean_closure_set(x_17, 0, x_2);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
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
lean_dec_ref(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_3, x_24, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_12);
x_34 = lean_alloc_closure((void*)(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1___boxed), 12, 3);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_21);
lean_closure_set(x_34, 2, x_12);
lean_inc(x_3);
x_35 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_st_ref_take(x_3, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
lean_ctor_set(x_42, 0, x_40);
x_46 = lean_st_ref_set(x_3, x_42, x_43);
lean_dec(x_3);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_ctor_set(x_35, 1, x_47);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_st_ref_set(x_3, x_49, x_43);
lean_dec(x_3);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
lean_ctor_set(x_35, 1, x_51);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_st_ref_take(x_3, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_st_ref_set(x_3, x_61, x_58);
lean_dec(x_3);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_35);
if (x_65 == 0)
{
return x_35;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_35, 0);
x_67 = lean_ctor_get(x_35, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_35);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_30);
if (x_69 == 0)
{
return x_30;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_30, 0);
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_30);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_dec(x_24);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_st_ref_set(x_3, x_74, x_25);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_12);
x_81 = lean_alloc_closure((void*)(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1___boxed), 12, 3);
lean_closure_set(x_81, 0, x_1);
lean_closure_set(x_81, 1, x_21);
lean_closure_set(x_81, 2, x_12);
lean_inc(x_3);
x_82 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_80, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_st_ref_take(x_3, x_84);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_st_ref_set(x_3, x_93, x_90);
lean_dec(x_3);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec_ref(x_94);
if (lean_is_scalar(x_85)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_85;
}
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_3);
x_97 = lean_ctor_get(x_82, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_99 = x_82;
} else {
 lean_dec_ref(x_82);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_ctor_get(x_77, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_103 = x_77;
} else {
 lean_dec_ref(x_77);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_18);
if (x_105 == 0)
{
return x_18;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_18, 0);
x_107 = lean_ctor_get(x_18, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_18);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_13);
if (x_109 == 0)
{
return x_13;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_13, 0);
x_111 = lean_ctor_get(x_13, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_13);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Meta_Grind_updateLastTag(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_st_ref_get(x_16, x_30);
lean_dec(x_16);
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
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_st_ref_get(x_16, x_30);
lean_dec(x_16);
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
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_st_ref_get(x_17, x_22);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_19, 1, x_28);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_st_ref_get(x_17, x_31);
lean_dec(x_17);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_st_ref_get(x_17, x_22);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_19, 1, x_28);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_st_ref_get(x_17, x_31);
lean_dec(x_17);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Meta_Grind_casesMatch(x_1, x_2, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_st_ref_get(x_17, x_22);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_19, 1, x_28);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_st_ref_get(x_17, x_31);
lean_dec(x_17);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Grind_markCaseSplitAsResolved(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_st_ref_get(x_16, x_30);
lean_dec(x_16);
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
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_st_ref_get(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec(x_15);
x_18 = lean_st_mk_ref(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_st_ref_get(x_19, x_24);
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set(x_25, 1, x_27);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_st_ref_get(x_19, x_33);
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
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
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_15, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_st_ref_take(x_3, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_21);
x_27 = lean_st_ref_set(x_3, x_23, x_24);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
lean_free_object(x_16);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec_ref(x_27);
x_32 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
lean_dec_ref(x_20);
x_35 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_83; lean_object* x_84; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_32);
lean_inc_ref(x_39);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__2___boxed), 10, 1);
lean_closure_set(x_83, 0, x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_38, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_st_ref_take(x_3, x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_536; uint8_t x_537; uint8_t x_541; 
x_93 = lean_ctor_get(x_90, 0);
lean_dec(x_93);
lean_ctor_set(x_90, 0, x_88);
x_94 = lean_st_ref_set(x_3, x_90, x_91);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec_ref(x_94);
lean_inc_ref(x_39);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_96, 0, x_39);
lean_inc_ref(x_39);
x_267 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 10, 1);
lean_closure_set(x_267, 0, x_39);
x_536 = lean_unsigned_to_nat(1u);
x_541 = lean_nat_dec_lt(x_536, x_33);
if (x_541 == 0)
{
x_537 = x_34;
goto block_540;
}
else
{
x_537 = x_541;
goto block_540;
}
block_266:
{
lean_object* x_109; 
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_109 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_112 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(x_39, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_111);
if (lean_obj_tag(x_112) == 0)
{
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_96);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_114);
lean_dec_ref(x_32);
x_115 = l_Lean_Meta_Grind_getGoal___redArg(x_100, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_118);
lean_dec_ref(x_114);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
x_120 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_118);
lean_inc(x_110);
x_121 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 11, 2);
lean_closure_set(x_121, 0, x_110);
lean_closure_set(x_121, 1, x_120);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_122 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_119, x_121, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_st_ref_take(x_100, x_124);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = !lean_is_exclusive(x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
lean_ctor_set(x_128, 0, x_126);
x_132 = lean_st_ref_set(x_100, x_128, x_129);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec_ref(x_132);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_125;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_133;
goto block_82;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_st_ref_set(x_100, x_135, x_129);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec_ref(x_136);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_125;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_137;
goto block_82;
}
}
else
{
uint8_t x_138; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_138 = !lean_is_exclusive(x_122);
if (x_138 == 0)
{
return x_122;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_122, 0);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_122);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec_ref(x_114);
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_142 = !lean_is_exclusive(x_115);
if (x_142 == 0)
{
return x_115;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_115, 0);
x_144 = lean_ctor_get(x_115, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_115);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; uint8_t x_147; 
lean_dec_ref(x_32);
x_146 = lean_ctor_get(x_112, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_112, 1);
lean_inc(x_148);
lean_dec_ref(x_112);
x_149 = l_Lean_Meta_Grind_getGoal___redArg(x_100, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_153 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_152, x_96, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_st_ref_take(x_100, x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_161 = !lean_is_exclusive(x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_159, 0);
lean_dec(x_162);
lean_ctor_set(x_159, 0, x_157);
x_163 = lean_st_ref_set(x_100, x_159, x_160);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_Meta_Grind_getGoal___redArg(x_100, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_110);
x_169 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_169, 0, x_110);
lean_closure_set(x_169, 1, x_156);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_170 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_168, x_169, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_st_ref_take(x_100, x_172);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = !lean_is_exclusive(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_176, 0);
lean_dec(x_179);
lean_ctor_set(x_176, 0, x_174);
x_180 = lean_st_ref_set(x_100, x_176, x_177);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_173;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_181;
goto block_82;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
lean_dec(x_176);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_st_ref_set(x_100, x_183, x_177);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec_ref(x_184);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_173;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_185;
goto block_82;
}
}
else
{
uint8_t x_186; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_186 = !lean_is_exclusive(x_170);
if (x_186 == 0)
{
return x_170;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_170, 0);
x_188 = lean_ctor_get(x_170, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_170);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_156);
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_190 = !lean_is_exclusive(x_165);
if (x_190 == 0)
{
return x_165;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_165, 0);
x_192 = lean_ctor_get(x_165, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_165);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_159, 1);
lean_inc(x_194);
lean_dec(x_159);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_157);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_st_ref_set(x_100, x_195, x_160);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l_Lean_Meta_Grind_getGoal___redArg(x_100, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
lean_inc(x_110);
x_202 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_202, 0, x_110);
lean_closure_set(x_202, 1, x_156);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_203 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_201, x_202, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_200);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_dec(x_204);
x_208 = lean_st_ref_take(x_100, x_205);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec_ref(x_208);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_st_ref_set(x_100, x_213, x_210);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec_ref(x_214);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_206;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_215;
goto block_82;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_216 = lean_ctor_get(x_203, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_203, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_218 = x_203;
} else {
 lean_dec_ref(x_203);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_156);
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_220 = lean_ctor_get(x_198, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_198, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_222 = x_198;
} else {
 lean_dec_ref(x_198);
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
uint8_t x_224; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_224 = !lean_is_exclusive(x_153);
if (x_224 == 0)
{
return x_153;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_153, 0);
x_226 = lean_ctor_get(x_153, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_153);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
x_228 = !lean_is_exclusive(x_149);
if (x_228 == 0)
{
return x_149;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_149, 0);
x_230 = lean_ctor_get(x_149, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_149);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec_ref(x_96);
x_232 = lean_ctor_get(x_112, 1);
lean_inc(x_232);
lean_dec_ref(x_112);
x_233 = l_Lean_Meta_Grind_getGoal___redArg(x_100, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec_ref(x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
lean_dec(x_234);
lean_inc_ref(x_39);
lean_inc(x_110);
x_237 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_237, 0, x_110);
lean_closure_set(x_237, 1, x_39);
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_238 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_236, x_237, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107, x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = lean_st_ref_take(x_100, x_240);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec_ref(x_243);
x_246 = !lean_is_exclusive(x_244);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_244, 0);
lean_dec(x_247);
lean_ctor_set(x_244, 0, x_242);
x_248 = lean_st_ref_set(x_100, x_244, x_245);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec_ref(x_248);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_241;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_249;
goto block_82;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
lean_dec(x_244);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_242);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_st_ref_set(x_100, x_251, x_245);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec_ref(x_252);
x_40 = x_110;
x_41 = x_97;
x_42 = x_98;
x_43 = x_99;
x_44 = x_241;
x_45 = x_100;
x_46 = x_101;
x_47 = x_102;
x_48 = x_103;
x_49 = x_104;
x_50 = x_105;
x_51 = x_106;
x_52 = x_107;
x_53 = x_253;
goto block_82;
}
}
else
{
uint8_t x_254; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_254 = !lean_is_exclusive(x_238);
if (x_254 == 0)
{
return x_238;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_238, 0);
x_256 = lean_ctor_get(x_238, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_238);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_39);
x_258 = !lean_is_exclusive(x_233);
if (x_258 == 0)
{
return x_233;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_233, 0);
x_260 = lean_ctor_get(x_233, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_233);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
}
else
{
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
return x_112;
}
}
else
{
uint8_t x_262; 
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
x_262 = !lean_is_exclusive(x_109);
if (x_262 == 0)
{
return x_109;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_109, 0);
x_264 = lean_ctor_get(x_109, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_109);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
block_535:
{
lean_object* x_270; 
x_270 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_95);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_Lean_Meta_Grind_SplitInfo_source(x_32);
lean_inc(x_274);
lean_inc(x_269);
lean_inc_ref(x_39);
x_275 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_275, 0, x_39);
lean_closure_set(x_275, 1, x_269);
lean_closure_set(x_275, 2, x_33);
lean_closure_set(x_275, 3, x_274);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_276 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_273, x_275, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_272);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec_ref(x_276);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_st_ref_take(x_3, x_278);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec_ref(x_280);
x_283 = !lean_is_exclusive(x_281);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_281, 0);
lean_dec(x_284);
lean_ctor_set(x_281, 0, x_279);
x_285 = lean_st_ref_set(x_3, x_281, x_282);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec_ref(x_285);
x_287 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec_ref(x_287);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_291 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_290, x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_289);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec_ref(x_291);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_st_ref_take(x_3, x_293);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec_ref(x_295);
x_298 = !lean_is_exclusive(x_296);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_299 = lean_ctor_get(x_296, 0);
lean_dec(x_299);
lean_ctor_set(x_296, 0, x_294);
x_300 = lean_st_ref_set(x_3, x_296, x_297);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec_ref(x_300);
x_302 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_303 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(x_302, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_301);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; uint8_t x_305; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec(x_87);
lean_dec_ref(x_2);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec_ref(x_303);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_306;
goto block_266;
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_303, 1);
lean_inc(x_307);
lean_dec_ref(x_303);
x_308 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec_ref(x_308);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
lean_dec(x_309);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_312 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_311, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_310);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec_ref(x_312);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_st_ref_take(x_3, x_314);
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_316, 0);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_320 = lean_ctor_get(x_316, 1);
x_321 = lean_ctor_get(x_318, 0);
lean_dec(x_321);
lean_ctor_set(x_318, 0, x_315);
x_322 = lean_st_ref_set(x_3, x_318, x_320);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_324 = lean_ctor_get(x_322, 1);
x_325 = lean_ctor_get(x_322, 0);
lean_dec(x_325);
lean_inc_ref(x_39);
x_326 = l_Lean_MessageData_ofExpr(x_39);
x_327 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
lean_ctor_set_tag(x_322, 7);
lean_ctor_set(x_322, 1, x_327);
lean_ctor_set(x_322, 0, x_326);
x_328 = l_Nat_reprFast(x_87);
x_329 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_329, 0, x_328);
x_330 = l_Lean_MessageData_ofFormat(x_329);
lean_ctor_set_tag(x_316, 7);
lean_ctor_set(x_316, 1, x_330);
lean_ctor_set(x_316, 0, x_322);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_331 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_302, x_316, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_324);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec_ref(x_331);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_332;
goto block_266;
}
else
{
uint8_t x_333; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_333 = !lean_is_exclusive(x_331);
if (x_333 == 0)
{
return x_331;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_331, 0);
x_335 = lean_ctor_get(x_331, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_331);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_337 = lean_ctor_get(x_322, 1);
lean_inc(x_337);
lean_dec(x_322);
lean_inc_ref(x_39);
x_338 = l_Lean_MessageData_ofExpr(x_39);
x_339 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
x_340 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Nat_reprFast(x_87);
x_342 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_342, 0, x_341);
x_343 = l_Lean_MessageData_ofFormat(x_342);
lean_ctor_set_tag(x_316, 7);
lean_ctor_set(x_316, 1, x_343);
lean_ctor_set(x_316, 0, x_340);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_344 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_302, x_316, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_337);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec_ref(x_344);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_345;
goto block_266;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_350 = lean_ctor_get(x_316, 1);
x_351 = lean_ctor_get(x_318, 1);
lean_inc(x_351);
lean_dec(x_318);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_315);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_st_ref_set(x_3, x_352, x_350);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
lean_inc_ref(x_39);
x_356 = l_Lean_MessageData_ofExpr(x_39);
x_357 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_355)) {
 x_358 = lean_alloc_ctor(7, 2, 0);
} else {
 x_358 = x_355;
 lean_ctor_set_tag(x_358, 7);
}
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Nat_reprFast(x_87);
x_360 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_360, 0, x_359);
x_361 = l_Lean_MessageData_ofFormat(x_360);
lean_ctor_set_tag(x_316, 7);
lean_ctor_set(x_316, 1, x_361);
lean_ctor_set(x_316, 0, x_358);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_362 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_302, x_316, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_354);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec_ref(x_362);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_363;
goto block_266;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_364 = lean_ctor_get(x_362, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_362, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_366 = x_362;
} else {
 lean_dec_ref(x_362);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_368 = lean_ctor_get(x_316, 0);
x_369 = lean_ctor_get(x_316, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_316);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_315);
lean_ctor_set(x_372, 1, x_370);
x_373 = lean_st_ref_set(x_3, x_372, x_369);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
lean_inc_ref(x_39);
x_376 = l_Lean_MessageData_ofExpr(x_39);
x_377 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_375)) {
 x_378 = lean_alloc_ctor(7, 2, 0);
} else {
 x_378 = x_375;
 lean_ctor_set_tag(x_378, 7);
}
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_379 = l_Nat_reprFast(x_87);
x_380 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_380, 0, x_379);
x_381 = l_Lean_MessageData_ofFormat(x_380);
x_382 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_382, 0, x_378);
lean_ctor_set(x_382, 1, x_381);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_383 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_302, x_382, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_374);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec_ref(x_383);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_384;
goto block_266;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_387 = x_383;
} else {
 lean_dec_ref(x_383);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_389 = !lean_is_exclusive(x_312);
if (x_389 == 0)
{
return x_312;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_312, 0);
x_391 = lean_ctor_get(x_312, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_312);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_393 = !lean_is_exclusive(x_308);
if (x_393 == 0)
{
return x_308;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_308, 0);
x_395 = lean_ctor_get(x_308, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_308);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
}
else
{
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_303;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_296, 1);
lean_inc(x_397);
lean_dec(x_296);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_294);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_st_ref_set(x_3, x_398, x_297);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec_ref(x_399);
x_401 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_402 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(x_401, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_400);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; uint8_t x_404; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_unbox(x_403);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; 
lean_dec(x_87);
lean_dec_ref(x_2);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec_ref(x_402);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_405;
goto block_266;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_402, 1);
lean_inc(x_406);
lean_dec_ref(x_402);
x_407 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_406);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec_ref(x_407);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
lean_dec(x_408);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_411 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_410, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_409);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec_ref(x_411);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_st_ref_take(x_3, x_413);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_418 = x_415;
} else {
 lean_dec_ref(x_415);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_420 = x_416;
} else {
 lean_dec_ref(x_416);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_414);
lean_ctor_set(x_421, 1, x_419);
x_422 = lean_st_ref_set(x_3, x_421, x_417);
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_424 = x_422;
} else {
 lean_dec_ref(x_422);
 x_424 = lean_box(0);
}
lean_inc_ref(x_39);
x_425 = l_Lean_MessageData_ofExpr(x_39);
x_426 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_424)) {
 x_427 = lean_alloc_ctor(7, 2, 0);
} else {
 x_427 = x_424;
 lean_ctor_set_tag(x_427, 7);
}
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
x_428 = l_Nat_reprFast(x_87);
x_429 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_430 = l_Lean_MessageData_ofFormat(x_429);
if (lean_is_scalar(x_418)) {
 x_431 = lean_alloc_ctor(7, 2, 0);
} else {
 x_431 = x_418;
 lean_ctor_set_tag(x_431, 7);
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_430);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_432 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_401, x_431, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_423);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec_ref(x_432);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_433;
goto block_266;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_438 = lean_ctor_get(x_411, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_411, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_440 = x_411;
} else {
 lean_dec_ref(x_411);
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
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_442 = lean_ctor_get(x_407, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_407, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_444 = x_407;
} else {
 lean_dec_ref(x_407);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
}
else
{
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_402;
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_446 = !lean_is_exclusive(x_291);
if (x_446 == 0)
{
return x_291;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_291, 0);
x_448 = lean_ctor_get(x_291, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_291);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_267);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_450 = !lean_is_exclusive(x_287);
if (x_450 == 0)
{
return x_287;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_287, 0);
x_452 = lean_ctor_get(x_287, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_287);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_281, 1);
lean_inc(x_454);
lean_dec(x_281);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_279);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_st_ref_set(x_3, x_455, x_282);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
lean_dec_ref(x_456);
x_458 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec_ref(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
lean_dec(x_459);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_462 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_461, x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_460);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec_ref(x_462);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = lean_st_ref_take(x_3, x_464);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec_ref(x_466);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_465);
lean_ctor_set(x_471, 1, x_469);
x_472 = lean_st_ref_set(x_3, x_471, x_468);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec_ref(x_472);
x_474 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_475 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(x_474, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_473);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; uint8_t x_477; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_unbox(x_476);
lean_dec(x_476);
if (x_477 == 0)
{
lean_object* x_478; 
lean_dec(x_87);
lean_dec_ref(x_2);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec_ref(x_475);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_478;
goto block_266;
}
else
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_475, 1);
lean_inc(x_479);
lean_dec_ref(x_475);
x_480 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec_ref(x_480);
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
lean_dec(x_481);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_484 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_483, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_482);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec_ref(x_484);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_st_ref_take(x_3, x_486);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_491 = x_488;
} else {
 lean_dec_ref(x_488);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_493 = x_489;
} else {
 lean_dec_ref(x_489);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_487);
lean_ctor_set(x_494, 1, x_492);
x_495 = lean_st_ref_set(x_3, x_494, x_490);
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_497 = x_495;
} else {
 lean_dec_ref(x_495);
 x_497 = lean_box(0);
}
lean_inc_ref(x_39);
x_498 = l_Lean_MessageData_ofExpr(x_39);
x_499 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_497)) {
 x_500 = lean_alloc_ctor(7, 2, 0);
} else {
 x_500 = x_497;
 lean_ctor_set_tag(x_500, 7);
}
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
x_501 = l_Nat_reprFast(x_87);
x_502 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_502, 0, x_501);
x_503 = l_Lean_MessageData_ofFormat(x_502);
if (lean_is_scalar(x_491)) {
 x_504 = lean_alloc_ctor(7, 2, 0);
} else {
 x_504 = x_491;
 lean_ctor_set_tag(x_504, 7);
}
lean_ctor_set(x_504, 0, x_500);
lean_ctor_set(x_504, 1, x_503);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_505 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_474, x_504, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_496);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec_ref(x_505);
x_97 = x_274;
x_98 = x_268;
x_99 = x_269;
x_100 = x_3;
x_101 = x_4;
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_506;
goto block_266;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_505, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_509 = x_505;
} else {
 lean_dec_ref(x_505);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_511 = lean_ctor_get(x_484, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_484, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_513 = x_484;
} else {
 lean_dec_ref(x_484);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_515 = lean_ctor_get(x_480, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_480, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_517 = x_480;
} else {
 lean_dec_ref(x_480);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
}
else
{
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_475;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_519 = lean_ctor_get(x_462, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_462, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_521 = x_462;
} else {
 lean_dec_ref(x_462);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
return x_522;
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_267);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_523 = lean_ctor_get(x_458, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_458, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_525 = x_458;
} else {
 lean_dec_ref(x_458);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(1, 2, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_524);
return x_526;
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_274);
lean_dec(x_269);
lean_dec_ref(x_267);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_527 = !lean_is_exclusive(x_276);
if (x_527 == 0)
{
return x_276;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_276, 0);
x_529 = lean_ctor_get(x_276, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_276);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_269);
lean_dec_ref(x_267);
lean_dec_ref(x_96);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_531 = !lean_is_exclusive(x_270);
if (x_531 == 0)
{
return x_270;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_270, 0);
x_533 = lean_ctor_get(x_270, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_270);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
block_540:
{
uint8_t x_538; 
x_538 = 1;
if (x_537 == 0)
{
lean_inc(x_87);
x_268 = x_538;
x_269 = x_87;
goto block_535;
}
else
{
lean_object* x_539; 
x_539 = lean_nat_add(x_87, x_536);
x_268 = x_538;
x_269 = x_539;
goto block_535;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_679; uint8_t x_680; lean_object* x_681; lean_object* x_778; uint8_t x_779; uint8_t x_783; 
x_542 = lean_ctor_get(x_90, 1);
lean_inc(x_542);
lean_dec(x_90);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_88);
lean_ctor_set(x_543, 1, x_542);
x_544 = lean_st_ref_set(x_3, x_543, x_91);
x_545 = lean_ctor_get(x_544, 1);
lean_inc(x_545);
lean_dec_ref(x_544);
lean_inc_ref(x_39);
x_546 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_546, 0, x_39);
lean_inc_ref(x_39);
x_679 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 10, 1);
lean_closure_set(x_679, 0, x_39);
x_778 = lean_unsigned_to_nat(1u);
x_783 = lean_nat_dec_lt(x_778, x_33);
if (x_783 == 0)
{
x_779 = x_34;
goto block_782;
}
else
{
x_779 = x_783;
goto block_782;
}
block_678:
{
lean_object* x_559; 
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc(x_555);
lean_inc_ref(x_554);
lean_inc(x_553);
lean_inc_ref(x_552);
lean_inc(x_551);
lean_inc(x_550);
x_559 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_550, x_551, x_552, x_553, x_554, x_555, x_556, x_557, x_558);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec_ref(x_559);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc(x_555);
lean_inc_ref(x_554);
lean_inc(x_553);
lean_inc_ref(x_552);
lean_inc(x_551);
lean_inc(x_550);
x_562 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(x_39, x_550, x_551, x_552, x_553, x_554, x_555, x_556, x_557, x_561);
if (lean_obj_tag(x_562) == 0)
{
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec_ref(x_546);
x_563 = lean_ctor_get(x_562, 1);
lean_inc(x_563);
lean_dec_ref(x_562);
x_564 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_564);
lean_dec_ref(x_32);
x_565 = l_Lean_Meta_Grind_getGoal___redArg(x_550, x_563);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec_ref(x_565);
x_568 = lean_ctor_get(x_564, 1);
lean_inc_ref(x_568);
lean_dec_ref(x_564);
x_569 = lean_ctor_get(x_566, 0);
lean_inc(x_569);
lean_dec(x_566);
x_570 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_568);
lean_inc(x_560);
x_571 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 11, 2);
lean_closure_set(x_571, 0, x_560);
lean_closure_set(x_571, 1, x_570);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc(x_555);
lean_inc_ref(x_554);
lean_inc(x_553);
lean_inc_ref(x_552);
lean_inc(x_551);
lean_inc(x_550);
x_572 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_569, x_571, x_550, x_551, x_552, x_553, x_554, x_555, x_556, x_557, x_567);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec_ref(x_572);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_573, 1);
lean_inc(x_576);
lean_dec(x_573);
x_577 = lean_st_ref_take(x_550, x_574);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec_ref(x_577);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_581 = x_578;
} else {
 lean_dec_ref(x_578);
 x_581 = lean_box(0);
}
if (lean_is_scalar(x_581)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_581;
}
lean_ctor_set(x_582, 0, x_576);
lean_ctor_set(x_582, 1, x_580);
x_583 = lean_st_ref_set(x_550, x_582, x_579);
x_584 = lean_ctor_get(x_583, 1);
lean_inc(x_584);
lean_dec_ref(x_583);
x_40 = x_560;
x_41 = x_547;
x_42 = x_548;
x_43 = x_549;
x_44 = x_575;
x_45 = x_550;
x_46 = x_551;
x_47 = x_552;
x_48 = x_553;
x_49 = x_554;
x_50 = x_555;
x_51 = x_556;
x_52 = x_557;
x_53 = x_584;
goto block_82;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_585 = lean_ctor_get(x_572, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_572, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_587 = x_572;
} else {
 lean_dec_ref(x_572);
 x_587 = lean_box(0);
}
if (lean_is_scalar(x_587)) {
 x_588 = lean_alloc_ctor(1, 2, 0);
} else {
 x_588 = x_587;
}
lean_ctor_set(x_588, 0, x_585);
lean_ctor_set(x_588, 1, x_586);
return x_588;
}
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec_ref(x_564);
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_589 = lean_ctor_get(x_565, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_565, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_591 = x_565;
} else {
 lean_dec_ref(x_565);
 x_591 = lean_box(0);
}
if (lean_is_scalar(x_591)) {
 x_592 = lean_alloc_ctor(1, 2, 0);
} else {
 x_592 = x_591;
}
lean_ctor_set(x_592, 0, x_589);
lean_ctor_set(x_592, 1, x_590);
return x_592;
}
}
else
{
lean_object* x_593; uint8_t x_594; 
lean_dec_ref(x_32);
x_593 = lean_ctor_get(x_562, 0);
lean_inc(x_593);
x_594 = lean_unbox(x_593);
lean_dec(x_593);
if (x_594 == 0)
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_ctor_get(x_562, 1);
lean_inc(x_595);
lean_dec_ref(x_562);
x_596 = l_Lean_Meta_Grind_getGoal___redArg(x_550, x_595);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec_ref(x_596);
x_599 = lean_ctor_get(x_597, 0);
lean_inc(x_599);
lean_dec(x_597);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc(x_555);
lean_inc_ref(x_554);
lean_inc(x_553);
lean_inc_ref(x_552);
lean_inc(x_551);
lean_inc(x_550);
x_600 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_599, x_546, x_550, x_551, x_552, x_553, x_554, x_555, x_556, x_557, x_598);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec_ref(x_600);
x_603 = lean_ctor_get(x_601, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_601, 1);
lean_inc(x_604);
lean_dec(x_601);
x_605 = lean_st_ref_take(x_550, x_602);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec_ref(x_605);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_609 = x_606;
} else {
 lean_dec_ref(x_606);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_604);
lean_ctor_set(x_610, 1, x_608);
x_611 = lean_st_ref_set(x_550, x_610, x_607);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
lean_dec_ref(x_611);
x_613 = l_Lean_Meta_Grind_getGoal___redArg(x_550, x_612);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec_ref(x_613);
x_616 = lean_ctor_get(x_614, 0);
lean_inc(x_616);
lean_dec(x_614);
lean_inc(x_560);
x_617 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_617, 0, x_560);
lean_closure_set(x_617, 1, x_603);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc(x_555);
lean_inc_ref(x_554);
lean_inc(x_553);
lean_inc_ref(x_552);
lean_inc(x_551);
lean_inc(x_550);
x_618 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_616, x_617, x_550, x_551, x_552, x_553, x_554, x_555, x_556, x_557, x_615);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
lean_dec_ref(x_618);
x_621 = lean_ctor_get(x_619, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_619, 1);
lean_inc(x_622);
lean_dec(x_619);
x_623 = lean_st_ref_take(x_550, x_620);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec_ref(x_623);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_627 = x_624;
} else {
 lean_dec_ref(x_624);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(0, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_622);
lean_ctor_set(x_628, 1, x_626);
x_629 = lean_st_ref_set(x_550, x_628, x_625);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec_ref(x_629);
x_40 = x_560;
x_41 = x_547;
x_42 = x_548;
x_43 = x_549;
x_44 = x_621;
x_45 = x_550;
x_46 = x_551;
x_47 = x_552;
x_48 = x_553;
x_49 = x_554;
x_50 = x_555;
x_51 = x_556;
x_52 = x_557;
x_53 = x_630;
goto block_82;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_631 = lean_ctor_get(x_618, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_618, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_633 = x_618;
} else {
 lean_dec_ref(x_618);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_631);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_603);
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_635 = lean_ctor_get(x_613, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_613, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_637 = x_613;
} else {
 lean_dec_ref(x_613);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_639 = lean_ctor_get(x_600, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_600, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_641 = x_600;
} else {
 lean_dec_ref(x_600);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
return x_642;
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_546);
lean_dec_ref(x_39);
x_643 = lean_ctor_get(x_596, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_596, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_645 = x_596;
} else {
 lean_dec_ref(x_596);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
lean_object* x_647; lean_object* x_648; 
lean_dec_ref(x_546);
x_647 = lean_ctor_get(x_562, 1);
lean_inc(x_647);
lean_dec_ref(x_562);
x_648 = l_Lean_Meta_Grind_getGoal___redArg(x_550, x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec_ref(x_648);
x_651 = lean_ctor_get(x_649, 0);
lean_inc(x_651);
lean_dec(x_649);
lean_inc_ref(x_39);
lean_inc(x_560);
x_652 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_652, 0, x_560);
lean_closure_set(x_652, 1, x_39);
lean_inc(x_557);
lean_inc_ref(x_556);
lean_inc(x_555);
lean_inc_ref(x_554);
lean_inc(x_553);
lean_inc_ref(x_552);
lean_inc(x_551);
lean_inc(x_550);
x_653 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_651, x_652, x_550, x_551, x_552, x_553, x_554, x_555, x_556, x_557, x_650);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec_ref(x_653);
x_656 = lean_ctor_get(x_654, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_654, 1);
lean_inc(x_657);
lean_dec(x_654);
x_658 = lean_st_ref_take(x_550, x_655);
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec_ref(x_658);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_662 = x_659;
} else {
 lean_dec_ref(x_659);
 x_662 = lean_box(0);
}
if (lean_is_scalar(x_662)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_662;
}
lean_ctor_set(x_663, 0, x_657);
lean_ctor_set(x_663, 1, x_661);
x_664 = lean_st_ref_set(x_550, x_663, x_660);
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec_ref(x_664);
x_40 = x_560;
x_41 = x_547;
x_42 = x_548;
x_43 = x_549;
x_44 = x_656;
x_45 = x_550;
x_46 = x_551;
x_47 = x_552;
x_48 = x_553;
x_49 = x_554;
x_50 = x_555;
x_51 = x_556;
x_52 = x_557;
x_53 = x_665;
goto block_82;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_666 = lean_ctor_get(x_653, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_653, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_668 = x_653;
} else {
 lean_dec_ref(x_653);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_39);
x_670 = lean_ctor_get(x_648, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_648, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_672 = x_648;
} else {
 lean_dec_ref(x_648);
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
}
}
else
{
lean_dec(x_560);
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_546);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
return x_562;
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_557);
lean_dec_ref(x_556);
lean_dec(x_555);
lean_dec_ref(x_554);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_547);
lean_dec_ref(x_546);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
x_674 = lean_ctor_get(x_559, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_559, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_676 = x_559;
} else {
 lean_dec_ref(x_559);
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
block_777:
{
lean_object* x_682; 
x_682 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_545);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec_ref(x_682);
x_685 = lean_ctor_get(x_683, 0);
lean_inc(x_685);
lean_dec(x_683);
x_686 = l_Lean_Meta_Grind_SplitInfo_source(x_32);
lean_inc(x_686);
lean_inc(x_681);
lean_inc_ref(x_39);
x_687 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_687, 0, x_39);
lean_closure_set(x_687, 1, x_681);
lean_closure_set(x_687, 2, x_33);
lean_closure_set(x_687, 3, x_686);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_688 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_685, x_687, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_684);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec_ref(x_688);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_st_ref_take(x_3, x_690);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec_ref(x_692);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_696 = x_693;
} else {
 lean_dec_ref(x_693);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_696;
}
lean_ctor_set(x_697, 0, x_691);
lean_ctor_set(x_697, 1, x_695);
x_698 = lean_st_ref_set(x_3, x_697, x_694);
x_699 = lean_ctor_get(x_698, 1);
lean_inc(x_699);
lean_dec_ref(x_698);
x_700 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_699);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec_ref(x_700);
x_703 = lean_ctor_get(x_701, 0);
lean_inc(x_703);
lean_dec(x_701);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_704 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_703, x_679, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_702);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
lean_dec_ref(x_704);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
lean_dec(x_705);
x_708 = lean_st_ref_take(x_3, x_706);
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec_ref(x_708);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_712 = x_709;
} else {
 lean_dec_ref(x_709);
 x_712 = lean_box(0);
}
if (lean_is_scalar(x_712)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_712;
}
lean_ctor_set(x_713, 0, x_707);
lean_ctor_set(x_713, 1, x_711);
x_714 = lean_st_ref_set(x_3, x_713, x_710);
x_715 = lean_ctor_get(x_714, 1);
lean_inc(x_715);
lean_dec_ref(x_714);
x_716 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_717 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(x_716, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_715);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; uint8_t x_719; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_unbox(x_718);
lean_dec(x_718);
if (x_719 == 0)
{
lean_object* x_720; 
lean_dec(x_87);
lean_dec_ref(x_2);
x_720 = lean_ctor_get(x_717, 1);
lean_inc(x_720);
lean_dec_ref(x_717);
x_547 = x_686;
x_548 = x_680;
x_549 = x_681;
x_550 = x_3;
x_551 = x_4;
x_552 = x_5;
x_553 = x_6;
x_554 = x_7;
x_555 = x_8;
x_556 = x_9;
x_557 = x_10;
x_558 = x_720;
goto block_678;
}
else
{
lean_object* x_721; lean_object* x_722; 
x_721 = lean_ctor_get(x_717, 1);
lean_inc(x_721);
lean_dec_ref(x_717);
x_722 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_721);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec_ref(x_722);
x_725 = lean_ctor_get(x_723, 0);
lean_inc(x_725);
lean_dec(x_723);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_726 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_725, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_724);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
lean_dec_ref(x_726);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_730 = lean_st_ref_take(x_3, x_728);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_733 = x_730;
} else {
 lean_dec_ref(x_730);
 x_733 = lean_box(0);
}
x_734 = lean_ctor_get(x_731, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_735 = x_731;
} else {
 lean_dec_ref(x_731);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_729);
lean_ctor_set(x_736, 1, x_734);
x_737 = lean_st_ref_set(x_3, x_736, x_732);
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_739 = x_737;
} else {
 lean_dec_ref(x_737);
 x_739 = lean_box(0);
}
lean_inc_ref(x_39);
x_740 = l_Lean_MessageData_ofExpr(x_39);
x_741 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_739)) {
 x_742 = lean_alloc_ctor(7, 2, 0);
} else {
 x_742 = x_739;
 lean_ctor_set_tag(x_742, 7);
}
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_741);
x_743 = l_Nat_reprFast(x_87);
x_744 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_744, 0, x_743);
x_745 = l_Lean_MessageData_ofFormat(x_744);
if (lean_is_scalar(x_733)) {
 x_746 = lean_alloc_ctor(7, 2, 0);
} else {
 x_746 = x_733;
 lean_ctor_set_tag(x_746, 7);
}
lean_ctor_set(x_746, 0, x_742);
lean_ctor_set(x_746, 1, x_745);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_747 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_716, x_746, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_738);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; 
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
lean_dec_ref(x_747);
x_547 = x_686;
x_548 = x_680;
x_549 = x_681;
x_550 = x_3;
x_551 = x_4;
x_552 = x_5;
x_553 = x_6;
x_554 = x_7;
x_555 = x_8;
x_556 = x_9;
x_557 = x_10;
x_558 = x_748;
goto block_678;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_546);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_749 = lean_ctor_get(x_747, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_747, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_751 = x_747;
} else {
 lean_dec_ref(x_747);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(1, 2, 0);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_749);
lean_ctor_set(x_752, 1, x_750);
return x_752;
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_753 = lean_ctor_get(x_726, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_726, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_755 = x_726;
} else {
 lean_dec_ref(x_726);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_755)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_755;
}
lean_ctor_set(x_756, 0, x_753);
lean_ctor_set(x_756, 1, x_754);
return x_756;
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_757 = lean_ctor_get(x_722, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_722, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 x_759 = x_722;
} else {
 lean_dec_ref(x_722);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_757);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
}
else
{
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_717;
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_761 = lean_ctor_get(x_704, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_704, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_763 = x_704;
} else {
 lean_dec_ref(x_704);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
return x_764;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_679);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_765 = lean_ctor_get(x_700, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_700, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_767 = x_700;
} else {
 lean_dec_ref(x_700);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_686);
lean_dec(x_681);
lean_dec_ref(x_679);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_769 = lean_ctor_get(x_688, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_688, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_771 = x_688;
} else {
 lean_dec_ref(x_688);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_681);
lean_dec_ref(x_679);
lean_dec_ref(x_546);
lean_dec(x_87);
lean_dec_ref(x_39);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_773 = lean_ctor_get(x_682, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_682, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_775 = x_682;
} else {
 lean_dec_ref(x_682);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_773);
lean_ctor_set(x_776, 1, x_774);
return x_776;
}
}
block_782:
{
uint8_t x_780; 
x_780 = 1;
if (x_779 == 0)
{
lean_inc(x_87);
x_680 = x_780;
x_681 = x_87;
goto block_777;
}
else
{
lean_object* x_781; 
x_781 = lean_nat_add(x_87, x_778);
x_680 = x_780;
x_681 = x_781;
goto block_777;
}
}
}
}
else
{
uint8_t x_784; 
lean_dec_ref(x_39);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_784 = !lean_is_exclusive(x_84);
if (x_784 == 0)
{
return x_84;
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_84, 0);
x_786 = lean_ctor_get(x_84, 1);
lean_inc(x_786);
lean_inc(x_785);
lean_dec(x_84);
x_787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_787, 0, x_785);
lean_ctor_set(x_787, 1, x_786);
return x_787;
}
}
block_82:
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Grind_getGoal___redArg(x_45, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = l_List_lengthTR___redArg(x_44);
x_58 = l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
x_59 = l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__1(x_55, x_39, x_57, x_41, x_44, x_58);
x_60 = l_Lean_mkMVar(x_40);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
x_61 = l_Lean_Meta_Grind_mkChoice(x_60, x_59, x_43, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Meta_Grind_intros(x_43, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(x_42);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(x_42);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
return x_63;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_78 = !lean_is_exclusive(x_54);
if (x_78 == 0)
{
return x_54;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_54, 0);
x_80 = lean_ctor_get(x_54, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_54);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_788; 
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_788 = !lean_is_exclusive(x_35);
if (x_788 == 0)
{
return x_35;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_35, 0);
x_790 = lean_ctor_get(x_35, 1);
lean_inc(x_790);
lean_inc(x_789);
lean_dec(x_35);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_790);
return x_791;
}
}
}
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_23, 1);
lean_inc(x_792);
lean_dec(x_23);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_21);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_st_ref_set(x_3, x_793, x_24);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_795; uint8_t x_796; lean_object* x_797; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
lean_dec_ref(x_794);
x_796 = 0;
x_797 = lean_box(x_796);
lean_ctor_set(x_16, 1, x_795);
lean_ctor_set(x_16, 0, x_797);
return x_16;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; 
lean_free_object(x_16);
x_798 = lean_ctor_get(x_794, 1);
lean_inc(x_798);
lean_dec_ref(x_794);
x_799 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_799);
x_800 = lean_ctor_get(x_20, 1);
lean_inc(x_800);
x_801 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
lean_dec_ref(x_20);
x_802 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_798);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_848; lean_object* x_849; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec_ref(x_802);
x_805 = lean_ctor_get(x_803, 0);
lean_inc(x_805);
lean_dec(x_803);
x_806 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_799);
lean_inc_ref(x_806);
x_848 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__2___boxed), 10, 1);
lean_closure_set(x_848, 0, x_806);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_849 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_805, x_848, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_804);
if (lean_obj_tag(x_849) == 0)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_995; uint8_t x_996; lean_object* x_997; lean_object* x_1094; uint8_t x_1095; uint8_t x_1099; 
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
lean_dec_ref(x_849);
x_852 = lean_ctor_get(x_850, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_850, 1);
lean_inc(x_853);
lean_dec(x_850);
x_854 = lean_st_ref_take(x_3, x_851);
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec_ref(x_854);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_858 = x_855;
} else {
 lean_dec_ref(x_855);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(0, 2, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_853);
lean_ctor_set(x_859, 1, x_857);
x_860 = lean_st_ref_set(x_3, x_859, x_856);
x_861 = lean_ctor_get(x_860, 1);
lean_inc(x_861);
lean_dec_ref(x_860);
lean_inc_ref(x_806);
x_862 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_862, 0, x_806);
lean_inc_ref(x_806);
x_995 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 10, 1);
lean_closure_set(x_995, 0, x_806);
x_1094 = lean_unsigned_to_nat(1u);
x_1099 = lean_nat_dec_lt(x_1094, x_800);
if (x_1099 == 0)
{
x_1095 = x_801;
goto block_1098;
}
else
{
x_1095 = x_1099;
goto block_1098;
}
block_994:
{
lean_object* x_875; 
lean_inc(x_873);
lean_inc_ref(x_872);
lean_inc(x_871);
lean_inc_ref(x_870);
lean_inc(x_869);
lean_inc_ref(x_868);
lean_inc(x_867);
lean_inc(x_866);
x_875 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_866, x_867, x_868, x_869, x_870, x_871, x_872, x_873, x_874);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec_ref(x_875);
lean_inc(x_873);
lean_inc_ref(x_872);
lean_inc(x_871);
lean_inc_ref(x_870);
lean_inc(x_869);
lean_inc_ref(x_868);
lean_inc(x_867);
lean_inc(x_866);
x_878 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(x_806, x_866, x_867, x_868, x_869, x_870, x_871, x_872, x_873, x_877);
if (lean_obj_tag(x_878) == 0)
{
if (lean_obj_tag(x_799) == 1)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec_ref(x_862);
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
lean_dec_ref(x_878);
x_880 = lean_ctor_get(x_799, 0);
lean_inc_ref(x_880);
lean_dec_ref(x_799);
x_881 = l_Lean_Meta_Grind_getGoal___redArg(x_866, x_879);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec_ref(x_881);
x_884 = lean_ctor_get(x_880, 1);
lean_inc_ref(x_884);
lean_dec_ref(x_880);
x_885 = lean_ctor_get(x_882, 0);
lean_inc(x_885);
lean_dec(x_882);
x_886 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_884);
lean_inc(x_876);
x_887 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 11, 2);
lean_closure_set(x_887, 0, x_876);
lean_closure_set(x_887, 1, x_886);
lean_inc(x_873);
lean_inc_ref(x_872);
lean_inc(x_871);
lean_inc_ref(x_870);
lean_inc(x_869);
lean_inc_ref(x_868);
lean_inc(x_867);
lean_inc(x_866);
x_888 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_885, x_887, x_866, x_867, x_868, x_869, x_870, x_871, x_872, x_873, x_883);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
lean_dec_ref(x_888);
x_891 = lean_ctor_get(x_889, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_889, 1);
lean_inc(x_892);
lean_dec(x_889);
x_893 = lean_st_ref_take(x_866, x_890);
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec_ref(x_893);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_897 = x_894;
} else {
 lean_dec_ref(x_894);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(0, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_892);
lean_ctor_set(x_898, 1, x_896);
x_899 = lean_st_ref_set(x_866, x_898, x_895);
x_900 = lean_ctor_get(x_899, 1);
lean_inc(x_900);
lean_dec_ref(x_899);
x_807 = x_876;
x_808 = x_863;
x_809 = x_864;
x_810 = x_865;
x_811 = x_891;
x_812 = x_866;
x_813 = x_867;
x_814 = x_868;
x_815 = x_869;
x_816 = x_870;
x_817 = x_871;
x_818 = x_872;
x_819 = x_873;
x_820 = x_900;
goto block_847;
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_901 = lean_ctor_get(x_888, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_888, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_903 = x_888;
} else {
 lean_dec_ref(x_888);
 x_903 = lean_box(0);
}
if (lean_is_scalar(x_903)) {
 x_904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_904 = x_903;
}
lean_ctor_set(x_904, 0, x_901);
lean_ctor_set(x_904, 1, x_902);
return x_904;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec_ref(x_880);
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_905 = lean_ctor_get(x_881, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_881, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 lean_ctor_release(x_881, 1);
 x_907 = x_881;
} else {
 lean_dec_ref(x_881);
 x_907 = lean_box(0);
}
if (lean_is_scalar(x_907)) {
 x_908 = lean_alloc_ctor(1, 2, 0);
} else {
 x_908 = x_907;
}
lean_ctor_set(x_908, 0, x_905);
lean_ctor_set(x_908, 1, x_906);
return x_908;
}
}
else
{
lean_object* x_909; uint8_t x_910; 
lean_dec_ref(x_799);
x_909 = lean_ctor_get(x_878, 0);
lean_inc(x_909);
x_910 = lean_unbox(x_909);
lean_dec(x_909);
if (x_910 == 0)
{
lean_object* x_911; lean_object* x_912; 
x_911 = lean_ctor_get(x_878, 1);
lean_inc(x_911);
lean_dec_ref(x_878);
x_912 = l_Lean_Meta_Grind_getGoal___redArg(x_866, x_911);
if (lean_obj_tag(x_912) == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec_ref(x_912);
x_915 = lean_ctor_get(x_913, 0);
lean_inc(x_915);
lean_dec(x_913);
lean_inc(x_873);
lean_inc_ref(x_872);
lean_inc(x_871);
lean_inc_ref(x_870);
lean_inc(x_869);
lean_inc_ref(x_868);
lean_inc(x_867);
lean_inc(x_866);
x_916 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_915, x_862, x_866, x_867, x_868, x_869, x_870, x_871, x_872, x_873, x_914);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
lean_dec_ref(x_916);
x_919 = lean_ctor_get(x_917, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_917, 1);
lean_inc(x_920);
lean_dec(x_917);
x_921 = lean_st_ref_take(x_866, x_918);
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
lean_dec_ref(x_921);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_925 = x_922;
} else {
 lean_dec_ref(x_922);
 x_925 = lean_box(0);
}
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(0, 2, 0);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_920);
lean_ctor_set(x_926, 1, x_924);
x_927 = lean_st_ref_set(x_866, x_926, x_923);
x_928 = lean_ctor_get(x_927, 1);
lean_inc(x_928);
lean_dec_ref(x_927);
x_929 = l_Lean_Meta_Grind_getGoal___redArg(x_866, x_928);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
lean_dec_ref(x_929);
x_932 = lean_ctor_get(x_930, 0);
lean_inc(x_932);
lean_dec(x_930);
lean_inc(x_876);
x_933 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_933, 0, x_876);
lean_closure_set(x_933, 1, x_919);
lean_inc(x_873);
lean_inc_ref(x_872);
lean_inc(x_871);
lean_inc_ref(x_870);
lean_inc(x_869);
lean_inc_ref(x_868);
lean_inc(x_867);
lean_inc(x_866);
x_934 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_932, x_933, x_866, x_867, x_868, x_869, x_870, x_871, x_872, x_873, x_931);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_934, 1);
lean_inc(x_936);
lean_dec_ref(x_934);
x_937 = lean_ctor_get(x_935, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_935, 1);
lean_inc(x_938);
lean_dec(x_935);
x_939 = lean_st_ref_take(x_866, x_936);
x_940 = lean_ctor_get(x_939, 0);
lean_inc(x_940);
x_941 = lean_ctor_get(x_939, 1);
lean_inc(x_941);
lean_dec_ref(x_939);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_943 = x_940;
} else {
 lean_dec_ref(x_940);
 x_943 = lean_box(0);
}
if (lean_is_scalar(x_943)) {
 x_944 = lean_alloc_ctor(0, 2, 0);
} else {
 x_944 = x_943;
}
lean_ctor_set(x_944, 0, x_938);
lean_ctor_set(x_944, 1, x_942);
x_945 = lean_st_ref_set(x_866, x_944, x_941);
x_946 = lean_ctor_get(x_945, 1);
lean_inc(x_946);
lean_dec_ref(x_945);
x_807 = x_876;
x_808 = x_863;
x_809 = x_864;
x_810 = x_865;
x_811 = x_937;
x_812 = x_866;
x_813 = x_867;
x_814 = x_868;
x_815 = x_869;
x_816 = x_870;
x_817 = x_871;
x_818 = x_872;
x_819 = x_873;
x_820 = x_946;
goto block_847;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_947 = lean_ctor_get(x_934, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_934, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_949 = x_934;
} else {
 lean_dec_ref(x_934);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_947);
lean_ctor_set(x_950, 1, x_948);
return x_950;
}
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_919);
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_951 = lean_ctor_get(x_929, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_929, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_953 = x_929;
} else {
 lean_dec_ref(x_929);
 x_953 = lean_box(0);
}
if (lean_is_scalar(x_953)) {
 x_954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_954 = x_953;
}
lean_ctor_set(x_954, 0, x_951);
lean_ctor_set(x_954, 1, x_952);
return x_954;
}
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_955 = lean_ctor_get(x_916, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_916, 1);
lean_inc(x_956);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_957 = x_916;
} else {
 lean_dec_ref(x_916);
 x_957 = lean_box(0);
}
if (lean_is_scalar(x_957)) {
 x_958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_958 = x_957;
}
lean_ctor_set(x_958, 0, x_955);
lean_ctor_set(x_958, 1, x_956);
return x_958;
}
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_862);
lean_dec_ref(x_806);
x_959 = lean_ctor_get(x_912, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_912, 1);
lean_inc(x_960);
if (lean_is_exclusive(x_912)) {
 lean_ctor_release(x_912, 0);
 lean_ctor_release(x_912, 1);
 x_961 = x_912;
} else {
 lean_dec_ref(x_912);
 x_961 = lean_box(0);
}
if (lean_is_scalar(x_961)) {
 x_962 = lean_alloc_ctor(1, 2, 0);
} else {
 x_962 = x_961;
}
lean_ctor_set(x_962, 0, x_959);
lean_ctor_set(x_962, 1, x_960);
return x_962;
}
}
else
{
lean_object* x_963; lean_object* x_964; 
lean_dec_ref(x_862);
x_963 = lean_ctor_get(x_878, 1);
lean_inc(x_963);
lean_dec_ref(x_878);
x_964 = l_Lean_Meta_Grind_getGoal___redArg(x_866, x_963);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec_ref(x_964);
x_967 = lean_ctor_get(x_965, 0);
lean_inc(x_967);
lean_dec(x_965);
lean_inc_ref(x_806);
lean_inc(x_876);
x_968 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_968, 0, x_876);
lean_closure_set(x_968, 1, x_806);
lean_inc(x_873);
lean_inc_ref(x_872);
lean_inc(x_871);
lean_inc_ref(x_870);
lean_inc(x_869);
lean_inc_ref(x_868);
lean_inc(x_867);
lean_inc(x_866);
x_969 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_967, x_968, x_866, x_867, x_868, x_869, x_870, x_871, x_872, x_873, x_966);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec_ref(x_969);
x_972 = lean_ctor_get(x_970, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_970, 1);
lean_inc(x_973);
lean_dec(x_970);
x_974 = lean_st_ref_take(x_866, x_971);
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
lean_dec_ref(x_974);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_978 = x_975;
} else {
 lean_dec_ref(x_975);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_979 = x_978;
}
lean_ctor_set(x_979, 0, x_973);
lean_ctor_set(x_979, 1, x_977);
x_980 = lean_st_ref_set(x_866, x_979, x_976);
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
lean_dec_ref(x_980);
x_807 = x_876;
x_808 = x_863;
x_809 = x_864;
x_810 = x_865;
x_811 = x_972;
x_812 = x_866;
x_813 = x_867;
x_814 = x_868;
x_815 = x_869;
x_816 = x_870;
x_817 = x_871;
x_818 = x_872;
x_819 = x_873;
x_820 = x_981;
goto block_847;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_982 = lean_ctor_get(x_969, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_969, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_984 = x_969;
} else {
 lean_dec_ref(x_969);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_806);
x_986 = lean_ctor_get(x_964, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_964, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_988 = x_964;
} else {
 lean_dec_ref(x_964);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
}
}
else
{
lean_dec(x_876);
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_862);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
return x_878;
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_873);
lean_dec_ref(x_872);
lean_dec(x_871);
lean_dec_ref(x_870);
lean_dec(x_869);
lean_dec_ref(x_868);
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_863);
lean_dec_ref(x_862);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
x_990 = lean_ctor_get(x_875, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_875, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_992 = x_875;
} else {
 lean_dec_ref(x_875);
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
block_1093:
{
lean_object* x_998; 
x_998 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_861);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec_ref(x_998);
x_1001 = lean_ctor_get(x_999, 0);
lean_inc(x_1001);
lean_dec(x_999);
x_1002 = l_Lean_Meta_Grind_SplitInfo_source(x_799);
lean_inc(x_1002);
lean_inc(x_997);
lean_inc_ref(x_806);
x_1003 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_1003, 0, x_806);
lean_closure_set(x_1003, 1, x_997);
lean_closure_set(x_1003, 2, x_800);
lean_closure_set(x_1003, 3, x_1002);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1004 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1001, x_1003, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1000);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
lean_dec_ref(x_1004);
x_1007 = lean_ctor_get(x_1005, 1);
lean_inc(x_1007);
lean_dec(x_1005);
x_1008 = lean_st_ref_take(x_3, x_1006);
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
lean_dec_ref(x_1008);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1012 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1012 = lean_box(0);
}
if (lean_is_scalar(x_1012)) {
 x_1013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1013 = x_1012;
}
lean_ctor_set(x_1013, 0, x_1007);
lean_ctor_set(x_1013, 1, x_1011);
x_1014 = lean_st_ref_set(x_3, x_1013, x_1010);
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
lean_dec_ref(x_1014);
x_1016 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1015);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec_ref(x_1016);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
lean_dec(x_1017);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1020 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1019, x_995, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1018);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1021 = lean_ctor_get(x_1020, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1020, 1);
lean_inc(x_1022);
lean_dec_ref(x_1020);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec(x_1021);
x_1024 = lean_st_ref_take(x_3, x_1022);
x_1025 = lean_ctor_get(x_1024, 0);
lean_inc(x_1025);
x_1026 = lean_ctor_get(x_1024, 1);
lean_inc(x_1026);
lean_dec_ref(x_1024);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 lean_ctor_release(x_1025, 1);
 x_1028 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1028 = lean_box(0);
}
if (lean_is_scalar(x_1028)) {
 x_1029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1029 = x_1028;
}
lean_ctor_set(x_1029, 0, x_1023);
lean_ctor_set(x_1029, 1, x_1027);
x_1030 = lean_st_ref_set(x_3, x_1029, x_1026);
x_1031 = lean_ctor_get(x_1030, 1);
lean_inc(x_1031);
lean_dec_ref(x_1030);
x_1032 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1033 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(x_1032, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1031);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; uint8_t x_1035; 
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
x_1035 = lean_unbox(x_1034);
lean_dec(x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; 
lean_dec(x_852);
lean_dec_ref(x_2);
x_1036 = lean_ctor_get(x_1033, 1);
lean_inc(x_1036);
lean_dec_ref(x_1033);
x_863 = x_1002;
x_864 = x_996;
x_865 = x_997;
x_866 = x_3;
x_867 = x_4;
x_868 = x_5;
x_869 = x_6;
x_870 = x_7;
x_871 = x_8;
x_872 = x_9;
x_873 = x_10;
x_874 = x_1036;
goto block_994;
}
else
{
lean_object* x_1037; lean_object* x_1038; 
x_1037 = lean_ctor_get(x_1033, 1);
lean_inc(x_1037);
lean_dec_ref(x_1033);
x_1038 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1037);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec_ref(x_1038);
x_1041 = lean_ctor_get(x_1039, 0);
lean_inc(x_1041);
lean_dec(x_1039);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1042 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1041, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1040);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1042, 1);
lean_inc(x_1044);
lean_dec_ref(x_1042);
x_1045 = lean_ctor_get(x_1043, 1);
lean_inc(x_1045);
lean_dec(x_1043);
x_1046 = lean_st_ref_take(x_3, x_1044);
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1049 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1049 = lean_box(0);
}
x_1050 = lean_ctor_get(x_1047, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1051 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1051 = lean_box(0);
}
if (lean_is_scalar(x_1051)) {
 x_1052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1052 = x_1051;
}
lean_ctor_set(x_1052, 0, x_1045);
lean_ctor_set(x_1052, 1, x_1050);
x_1053 = lean_st_ref_set(x_3, x_1052, x_1048);
x_1054 = lean_ctor_get(x_1053, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1055 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1055 = lean_box(0);
}
lean_inc_ref(x_806);
x_1056 = l_Lean_MessageData_ofExpr(x_806);
x_1057 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_1055)) {
 x_1058 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1058 = x_1055;
 lean_ctor_set_tag(x_1058, 7);
}
lean_ctor_set(x_1058, 0, x_1056);
lean_ctor_set(x_1058, 1, x_1057);
x_1059 = l_Nat_reprFast(x_852);
x_1060 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1060, 0, x_1059);
x_1061 = l_Lean_MessageData_ofFormat(x_1060);
if (lean_is_scalar(x_1049)) {
 x_1062 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1062 = x_1049;
 lean_ctor_set_tag(x_1062, 7);
}
lean_ctor_set(x_1062, 0, x_1058);
lean_ctor_set(x_1062, 1, x_1061);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1063 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_1032, x_1062, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1054);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; 
x_1064 = lean_ctor_get(x_1063, 1);
lean_inc(x_1064);
lean_dec_ref(x_1063);
x_863 = x_1002;
x_864 = x_996;
x_865 = x_997;
x_866 = x_3;
x_867 = x_4;
x_868 = x_5;
x_869 = x_6;
x_870 = x_7;
x_871 = x_8;
x_872 = x_9;
x_873 = x_10;
x_874 = x_1064;
goto block_994;
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_862);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1065 = lean_ctor_get(x_1063, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1063, 1);
lean_inc(x_1066);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1067 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1067 = lean_box(0);
}
if (lean_is_scalar(x_1067)) {
 x_1068 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1068 = x_1067;
}
lean_ctor_set(x_1068, 0, x_1065);
lean_ctor_set(x_1068, 1, x_1066);
return x_1068;
}
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1069 = lean_ctor_get(x_1042, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1042, 1);
lean_inc(x_1070);
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 lean_ctor_release(x_1042, 1);
 x_1071 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1071 = lean_box(0);
}
if (lean_is_scalar(x_1071)) {
 x_1072 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1072 = x_1071;
}
lean_ctor_set(x_1072, 0, x_1069);
lean_ctor_set(x_1072, 1, x_1070);
return x_1072;
}
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1073 = lean_ctor_get(x_1038, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1038, 1);
lean_inc(x_1074);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1075 = x_1038;
} else {
 lean_dec_ref(x_1038);
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
}
else
{
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1033;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1077 = lean_ctor_get(x_1020, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1020, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 x_1079 = x_1020;
} else {
 lean_dec_ref(x_1020);
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
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_995);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1081 = lean_ctor_get(x_1016, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1016, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1083 = x_1016;
} else {
 lean_dec_ref(x_1016);
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
lean_dec(x_1002);
lean_dec(x_997);
lean_dec_ref(x_995);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1085 = lean_ctor_get(x_1004, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1004, 1);
lean_inc(x_1086);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1087 = x_1004;
} else {
 lean_dec_ref(x_1004);
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
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_997);
lean_dec_ref(x_995);
lean_dec_ref(x_862);
lean_dec(x_852);
lean_dec_ref(x_806);
lean_dec(x_800);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1089 = lean_ctor_get(x_998, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_998, 1);
lean_inc(x_1090);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1091 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1091 = lean_box(0);
}
if (lean_is_scalar(x_1091)) {
 x_1092 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1092 = x_1091;
}
lean_ctor_set(x_1092, 0, x_1089);
lean_ctor_set(x_1092, 1, x_1090);
return x_1092;
}
}
block_1098:
{
uint8_t x_1096; 
x_1096 = 1;
if (x_1095 == 0)
{
lean_inc(x_852);
x_996 = x_1096;
x_997 = x_852;
goto block_1093;
}
else
{
lean_object* x_1097; 
x_1097 = lean_nat_add(x_852, x_1094);
x_996 = x_1096;
x_997 = x_1097;
goto block_1093;
}
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec_ref(x_806);
lean_dec(x_800);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1100 = lean_ctor_get(x_849, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_849, 1);
lean_inc(x_1101);
if (lean_is_exclusive(x_849)) {
 lean_ctor_release(x_849, 0);
 lean_ctor_release(x_849, 1);
 x_1102 = x_849;
} else {
 lean_dec_ref(x_849);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1101);
return x_1103;
}
block_847:
{
lean_object* x_821; 
x_821 = l_Lean_Meta_Grind_getGoal___redArg(x_812, x_820);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec_ref(x_821);
x_824 = l_List_lengthTR___redArg(x_811);
x_825 = l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
x_826 = l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__1(x_822, x_806, x_824, x_808, x_811, x_825);
x_827 = l_Lean_mkMVar(x_807);
lean_inc(x_819);
lean_inc_ref(x_818);
lean_inc(x_817);
lean_inc_ref(x_816);
lean_inc(x_815);
lean_inc_ref(x_814);
lean_inc(x_813);
lean_inc(x_812);
lean_inc(x_810);
x_828 = l_Lean_Meta_Grind_mkChoice(x_827, x_826, x_810, x_812, x_813, x_814, x_815, x_816, x_817, x_818, x_819, x_823);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; 
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
lean_dec_ref(x_828);
x_830 = l_Lean_Meta_Grind_intros(x_810, x_812, x_813, x_814, x_815, x_816, x_817, x_818, x_819, x_829);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_831 = lean_ctor_get(x_830, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_832 = x_830;
} else {
 lean_dec_ref(x_830);
 x_832 = lean_box(0);
}
x_833 = lean_box(x_809);
if (lean_is_scalar(x_832)) {
 x_834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_834 = x_832;
}
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_831);
return x_834;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_835 = lean_ctor_get(x_830, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_830, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_837 = x_830;
} else {
 lean_dec_ref(x_830);
 x_837 = lean_box(0);
}
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_837;
}
lean_ctor_set(x_838, 0, x_835);
lean_ctor_set(x_838, 1, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_819);
lean_dec_ref(x_818);
lean_dec(x_817);
lean_dec_ref(x_816);
lean_dec(x_815);
lean_dec_ref(x_814);
lean_dec(x_813);
lean_dec(x_812);
lean_dec(x_810);
x_839 = lean_ctor_get(x_828, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_828, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_841 = x_828;
} else {
 lean_dec_ref(x_828);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_840);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_819);
lean_dec_ref(x_818);
lean_dec(x_817);
lean_dec_ref(x_816);
lean_dec(x_815);
lean_dec_ref(x_814);
lean_dec(x_813);
lean_dec(x_812);
lean_dec(x_811);
lean_dec(x_810);
lean_dec(x_808);
lean_dec(x_807);
lean_dec_ref(x_806);
x_843 = lean_ctor_get(x_821, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_821, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_845 = x_821;
} else {
 lean_dec_ref(x_821);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
lean_dec(x_800);
lean_dec_ref(x_799);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1104 = lean_ctor_get(x_802, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_802, 1);
lean_inc(x_1105);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_1106 = x_802;
} else {
 lean_dec_ref(x_802);
 x_1106 = lean_box(0);
}
if (lean_is_scalar(x_1106)) {
 x_1107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1107 = x_1106;
}
lean_ctor_set(x_1107, 0, x_1104);
lean_ctor_set(x_1107, 1, x_1105);
return x_1107;
}
}
}
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1108 = lean_ctor_get(x_16, 0);
x_1109 = lean_ctor_get(x_16, 1);
lean_inc(x_1109);
lean_inc(x_1108);
lean_dec(x_16);
x_1110 = lean_ctor_get(x_1108, 0);
lean_inc(x_1110);
x_1111 = lean_ctor_get(x_1108, 1);
lean_inc(x_1111);
lean_dec(x_1108);
x_1112 = lean_st_ref_take(x_3, x_1109);
x_1113 = lean_ctor_get(x_1112, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1112, 1);
lean_inc(x_1114);
lean_dec_ref(x_1112);
x_1115 = lean_ctor_get(x_1113, 1);
lean_inc(x_1115);
if (lean_is_exclusive(x_1113)) {
 lean_ctor_release(x_1113, 0);
 lean_ctor_release(x_1113, 1);
 x_1116 = x_1113;
} else {
 lean_dec_ref(x_1113);
 x_1116 = lean_box(0);
}
if (lean_is_scalar(x_1116)) {
 x_1117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1117 = x_1116;
}
lean_ctor_set(x_1117, 0, x_1111);
lean_ctor_set(x_1117, 1, x_1115);
x_1118 = lean_st_ref_set(x_3, x_1117, x_1114);
if (lean_obj_tag(x_1110) == 0)
{
lean_object* x_1119; uint8_t x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1119 = lean_ctor_get(x_1118, 1);
lean_inc(x_1119);
lean_dec_ref(x_1118);
x_1120 = 0;
x_1121 = lean_box(x_1120);
x_1122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1122, 0, x_1121);
lean_ctor_set(x_1122, 1, x_1119);
return x_1122;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; lean_object* x_1127; 
x_1123 = lean_ctor_get(x_1118, 1);
lean_inc(x_1123);
lean_dec_ref(x_1118);
x_1124 = lean_ctor_get(x_1110, 0);
lean_inc_ref(x_1124);
x_1125 = lean_ctor_get(x_1110, 1);
lean_inc(x_1125);
x_1126 = lean_ctor_get_uint8(x_1110, sizeof(void*)*2);
lean_dec_ref(x_1110);
x_1127 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1123);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1173; lean_object* x_1174; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1127, 1);
lean_inc(x_1129);
lean_dec_ref(x_1127);
x_1130 = lean_ctor_get(x_1128, 0);
lean_inc(x_1130);
lean_dec(x_1128);
x_1131 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_1124);
lean_inc_ref(x_1131);
x_1173 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__2___boxed), 10, 1);
lean_closure_set(x_1173, 0, x_1131);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1174 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1130, x_1173, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1129);
if (lean_obj_tag(x_1174) == 0)
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1320; uint8_t x_1321; lean_object* x_1322; lean_object* x_1419; uint8_t x_1420; uint8_t x_1424; 
x_1175 = lean_ctor_get(x_1174, 0);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1174, 1);
lean_inc(x_1176);
lean_dec_ref(x_1174);
x_1177 = lean_ctor_get(x_1175, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1175, 1);
lean_inc(x_1178);
lean_dec(x_1175);
x_1179 = lean_st_ref_take(x_3, x_1176);
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
lean_dec_ref(x_1179);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 lean_ctor_release(x_1180, 1);
 x_1183 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1183 = lean_box(0);
}
if (lean_is_scalar(x_1183)) {
 x_1184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1184 = x_1183;
}
lean_ctor_set(x_1184, 0, x_1178);
lean_ctor_set(x_1184, 1, x_1182);
x_1185 = lean_st_ref_set(x_3, x_1184, x_1181);
x_1186 = lean_ctor_get(x_1185, 1);
lean_inc(x_1186);
lean_dec_ref(x_1185);
lean_inc_ref(x_1131);
x_1187 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_1187, 0, x_1131);
lean_inc_ref(x_1131);
x_1320 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 10, 1);
lean_closure_set(x_1320, 0, x_1131);
x_1419 = lean_unsigned_to_nat(1u);
x_1424 = lean_nat_dec_lt(x_1419, x_1125);
if (x_1424 == 0)
{
x_1420 = x_1126;
goto block_1423;
}
else
{
x_1420 = x_1424;
goto block_1423;
}
block_1319:
{
lean_object* x_1200; 
lean_inc(x_1198);
lean_inc_ref(x_1197);
lean_inc(x_1196);
lean_inc_ref(x_1195);
lean_inc(x_1194);
lean_inc_ref(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
x_1200 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_1191, x_1192, x_1193, x_1194, x_1195, x_1196, x_1197, x_1198, x_1199);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec_ref(x_1200);
lean_inc(x_1198);
lean_inc_ref(x_1197);
lean_inc(x_1196);
lean_inc_ref(x_1195);
lean_inc(x_1194);
lean_inc_ref(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
x_1203 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(x_1131, x_1191, x_1192, x_1193, x_1194, x_1195, x_1196, x_1197, x_1198, x_1202);
if (lean_obj_tag(x_1203) == 0)
{
if (lean_obj_tag(x_1124) == 1)
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
lean_dec_ref(x_1187);
x_1204 = lean_ctor_get(x_1203, 1);
lean_inc(x_1204);
lean_dec_ref(x_1203);
x_1205 = lean_ctor_get(x_1124, 0);
lean_inc_ref(x_1205);
lean_dec_ref(x_1124);
x_1206 = l_Lean_Meta_Grind_getGoal___redArg(x_1191, x_1204);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec_ref(x_1206);
x_1209 = lean_ctor_get(x_1205, 1);
lean_inc_ref(x_1209);
lean_dec_ref(x_1205);
x_1210 = lean_ctor_get(x_1207, 0);
lean_inc(x_1210);
lean_dec(x_1207);
x_1211 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_1209);
lean_inc(x_1201);
x_1212 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 11, 2);
lean_closure_set(x_1212, 0, x_1201);
lean_closure_set(x_1212, 1, x_1211);
lean_inc(x_1198);
lean_inc_ref(x_1197);
lean_inc(x_1196);
lean_inc_ref(x_1195);
lean_inc(x_1194);
lean_inc_ref(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
x_1213 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1210, x_1212, x_1191, x_1192, x_1193, x_1194, x_1195, x_1196, x_1197, x_1198, x_1208);
if (lean_obj_tag(x_1213) == 0)
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
x_1214 = lean_ctor_get(x_1213, 0);
lean_inc(x_1214);
x_1215 = lean_ctor_get(x_1213, 1);
lean_inc(x_1215);
lean_dec_ref(x_1213);
x_1216 = lean_ctor_get(x_1214, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1214, 1);
lean_inc(x_1217);
lean_dec(x_1214);
x_1218 = lean_st_ref_take(x_1191, x_1215);
x_1219 = lean_ctor_get(x_1218, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1218, 1);
lean_inc(x_1220);
lean_dec_ref(x_1218);
x_1221 = lean_ctor_get(x_1219, 1);
lean_inc(x_1221);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 x_1222 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1222 = lean_box(0);
}
if (lean_is_scalar(x_1222)) {
 x_1223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1223 = x_1222;
}
lean_ctor_set(x_1223, 0, x_1217);
lean_ctor_set(x_1223, 1, x_1221);
x_1224 = lean_st_ref_set(x_1191, x_1223, x_1220);
x_1225 = lean_ctor_get(x_1224, 1);
lean_inc(x_1225);
lean_dec_ref(x_1224);
x_1132 = x_1201;
x_1133 = x_1188;
x_1134 = x_1189;
x_1135 = x_1190;
x_1136 = x_1216;
x_1137 = x_1191;
x_1138 = x_1192;
x_1139 = x_1193;
x_1140 = x_1194;
x_1141 = x_1195;
x_1142 = x_1196;
x_1143 = x_1197;
x_1144 = x_1198;
x_1145 = x_1225;
goto block_1172;
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1226 = lean_ctor_get(x_1213, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1213, 1);
lean_inc(x_1227);
if (lean_is_exclusive(x_1213)) {
 lean_ctor_release(x_1213, 0);
 lean_ctor_release(x_1213, 1);
 x_1228 = x_1213;
} else {
 lean_dec_ref(x_1213);
 x_1228 = lean_box(0);
}
if (lean_is_scalar(x_1228)) {
 x_1229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1229 = x_1228;
}
lean_ctor_set(x_1229, 0, x_1226);
lean_ctor_set(x_1229, 1, x_1227);
return x_1229;
}
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec_ref(x_1205);
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1230 = lean_ctor_get(x_1206, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1206, 1);
lean_inc(x_1231);
if (lean_is_exclusive(x_1206)) {
 lean_ctor_release(x_1206, 0);
 lean_ctor_release(x_1206, 1);
 x_1232 = x_1206;
} else {
 lean_dec_ref(x_1206);
 x_1232 = lean_box(0);
}
if (lean_is_scalar(x_1232)) {
 x_1233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1233 = x_1232;
}
lean_ctor_set(x_1233, 0, x_1230);
lean_ctor_set(x_1233, 1, x_1231);
return x_1233;
}
}
else
{
lean_object* x_1234; uint8_t x_1235; 
lean_dec_ref(x_1124);
x_1234 = lean_ctor_get(x_1203, 0);
lean_inc(x_1234);
x_1235 = lean_unbox(x_1234);
lean_dec(x_1234);
if (x_1235 == 0)
{
lean_object* x_1236; lean_object* x_1237; 
x_1236 = lean_ctor_get(x_1203, 1);
lean_inc(x_1236);
lean_dec_ref(x_1203);
x_1237 = l_Lean_Meta_Grind_getGoal___redArg(x_1191, x_1236);
if (lean_obj_tag(x_1237) == 0)
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
x_1238 = lean_ctor_get(x_1237, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1237, 1);
lean_inc(x_1239);
lean_dec_ref(x_1237);
x_1240 = lean_ctor_get(x_1238, 0);
lean_inc(x_1240);
lean_dec(x_1238);
lean_inc(x_1198);
lean_inc_ref(x_1197);
lean_inc(x_1196);
lean_inc_ref(x_1195);
lean_inc(x_1194);
lean_inc_ref(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
x_1241 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1240, x_1187, x_1191, x_1192, x_1193, x_1194, x_1195, x_1196, x_1197, x_1198, x_1239);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1241, 1);
lean_inc(x_1243);
lean_dec_ref(x_1241);
x_1244 = lean_ctor_get(x_1242, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1242, 1);
lean_inc(x_1245);
lean_dec(x_1242);
x_1246 = lean_st_ref_take(x_1191, x_1243);
x_1247 = lean_ctor_get(x_1246, 0);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_1246, 1);
lean_inc(x_1248);
lean_dec_ref(x_1246);
x_1249 = lean_ctor_get(x_1247, 1);
lean_inc(x_1249);
if (lean_is_exclusive(x_1247)) {
 lean_ctor_release(x_1247, 0);
 lean_ctor_release(x_1247, 1);
 x_1250 = x_1247;
} else {
 lean_dec_ref(x_1247);
 x_1250 = lean_box(0);
}
if (lean_is_scalar(x_1250)) {
 x_1251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1251 = x_1250;
}
lean_ctor_set(x_1251, 0, x_1245);
lean_ctor_set(x_1251, 1, x_1249);
x_1252 = lean_st_ref_set(x_1191, x_1251, x_1248);
x_1253 = lean_ctor_get(x_1252, 1);
lean_inc(x_1253);
lean_dec_ref(x_1252);
x_1254 = l_Lean_Meta_Grind_getGoal___redArg(x_1191, x_1253);
if (lean_obj_tag(x_1254) == 0)
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1255 = lean_ctor_get(x_1254, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1254, 1);
lean_inc(x_1256);
lean_dec_ref(x_1254);
x_1257 = lean_ctor_get(x_1255, 0);
lean_inc(x_1257);
lean_dec(x_1255);
lean_inc(x_1201);
x_1258 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_1258, 0, x_1201);
lean_closure_set(x_1258, 1, x_1244);
lean_inc(x_1198);
lean_inc_ref(x_1197);
lean_inc(x_1196);
lean_inc_ref(x_1195);
lean_inc(x_1194);
lean_inc_ref(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
x_1259 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1257, x_1258, x_1191, x_1192, x_1193, x_1194, x_1195, x_1196, x_1197, x_1198, x_1256);
if (lean_obj_tag(x_1259) == 0)
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
x_1260 = lean_ctor_get(x_1259, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1259, 1);
lean_inc(x_1261);
lean_dec_ref(x_1259);
x_1262 = lean_ctor_get(x_1260, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1260, 1);
lean_inc(x_1263);
lean_dec(x_1260);
x_1264 = lean_st_ref_take(x_1191, x_1261);
x_1265 = lean_ctor_get(x_1264, 0);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1264, 1);
lean_inc(x_1266);
lean_dec_ref(x_1264);
x_1267 = lean_ctor_get(x_1265, 1);
lean_inc(x_1267);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 x_1268 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1268 = lean_box(0);
}
if (lean_is_scalar(x_1268)) {
 x_1269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1269 = x_1268;
}
lean_ctor_set(x_1269, 0, x_1263);
lean_ctor_set(x_1269, 1, x_1267);
x_1270 = lean_st_ref_set(x_1191, x_1269, x_1266);
x_1271 = lean_ctor_get(x_1270, 1);
lean_inc(x_1271);
lean_dec_ref(x_1270);
x_1132 = x_1201;
x_1133 = x_1188;
x_1134 = x_1189;
x_1135 = x_1190;
x_1136 = x_1262;
x_1137 = x_1191;
x_1138 = x_1192;
x_1139 = x_1193;
x_1140 = x_1194;
x_1141 = x_1195;
x_1142 = x_1196;
x_1143 = x_1197;
x_1144 = x_1198;
x_1145 = x_1271;
goto block_1172;
}
else
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1272 = lean_ctor_get(x_1259, 0);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1259, 1);
lean_inc(x_1273);
if (lean_is_exclusive(x_1259)) {
 lean_ctor_release(x_1259, 0);
 lean_ctor_release(x_1259, 1);
 x_1274 = x_1259;
} else {
 lean_dec_ref(x_1259);
 x_1274 = lean_box(0);
}
if (lean_is_scalar(x_1274)) {
 x_1275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1275 = x_1274;
}
lean_ctor_set(x_1275, 0, x_1272);
lean_ctor_set(x_1275, 1, x_1273);
return x_1275;
}
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
lean_dec(x_1244);
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1276 = lean_ctor_get(x_1254, 0);
lean_inc(x_1276);
x_1277 = lean_ctor_get(x_1254, 1);
lean_inc(x_1277);
if (lean_is_exclusive(x_1254)) {
 lean_ctor_release(x_1254, 0);
 lean_ctor_release(x_1254, 1);
 x_1278 = x_1254;
} else {
 lean_dec_ref(x_1254);
 x_1278 = lean_box(0);
}
if (lean_is_scalar(x_1278)) {
 x_1279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1279 = x_1278;
}
lean_ctor_set(x_1279, 0, x_1276);
lean_ctor_set(x_1279, 1, x_1277);
return x_1279;
}
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1280 = lean_ctor_get(x_1241, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1241, 1);
lean_inc(x_1281);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 lean_ctor_release(x_1241, 1);
 x_1282 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1282 = lean_box(0);
}
if (lean_is_scalar(x_1282)) {
 x_1283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1283 = x_1282;
}
lean_ctor_set(x_1283, 0, x_1280);
lean_ctor_set(x_1283, 1, x_1281);
return x_1283;
}
}
else
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1131);
x_1284 = lean_ctor_get(x_1237, 0);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_1237, 1);
lean_inc(x_1285);
if (lean_is_exclusive(x_1237)) {
 lean_ctor_release(x_1237, 0);
 lean_ctor_release(x_1237, 1);
 x_1286 = x_1237;
} else {
 lean_dec_ref(x_1237);
 x_1286 = lean_box(0);
}
if (lean_is_scalar(x_1286)) {
 x_1287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1287 = x_1286;
}
lean_ctor_set(x_1287, 0, x_1284);
lean_ctor_set(x_1287, 1, x_1285);
return x_1287;
}
}
else
{
lean_object* x_1288; lean_object* x_1289; 
lean_dec_ref(x_1187);
x_1288 = lean_ctor_get(x_1203, 1);
lean_inc(x_1288);
lean_dec_ref(x_1203);
x_1289 = l_Lean_Meta_Grind_getGoal___redArg(x_1191, x_1288);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
lean_dec_ref(x_1289);
x_1292 = lean_ctor_get(x_1290, 0);
lean_inc(x_1292);
lean_dec(x_1290);
lean_inc_ref(x_1131);
lean_inc(x_1201);
x_1293 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_1293, 0, x_1201);
lean_closure_set(x_1293, 1, x_1131);
lean_inc(x_1198);
lean_inc_ref(x_1197);
lean_inc(x_1196);
lean_inc_ref(x_1195);
lean_inc(x_1194);
lean_inc_ref(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
x_1294 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1292, x_1293, x_1191, x_1192, x_1193, x_1194, x_1195, x_1196, x_1197, x_1198, x_1291);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1295 = lean_ctor_get(x_1294, 0);
lean_inc(x_1295);
x_1296 = lean_ctor_get(x_1294, 1);
lean_inc(x_1296);
lean_dec_ref(x_1294);
x_1297 = lean_ctor_get(x_1295, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1295, 1);
lean_inc(x_1298);
lean_dec(x_1295);
x_1299 = lean_st_ref_take(x_1191, x_1296);
x_1300 = lean_ctor_get(x_1299, 0);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_1299, 1);
lean_inc(x_1301);
lean_dec_ref(x_1299);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
if (lean_is_exclusive(x_1300)) {
 lean_ctor_release(x_1300, 0);
 lean_ctor_release(x_1300, 1);
 x_1303 = x_1300;
} else {
 lean_dec_ref(x_1300);
 x_1303 = lean_box(0);
}
if (lean_is_scalar(x_1303)) {
 x_1304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1304 = x_1303;
}
lean_ctor_set(x_1304, 0, x_1298);
lean_ctor_set(x_1304, 1, x_1302);
x_1305 = lean_st_ref_set(x_1191, x_1304, x_1301);
x_1306 = lean_ctor_get(x_1305, 1);
lean_inc(x_1306);
lean_dec_ref(x_1305);
x_1132 = x_1201;
x_1133 = x_1188;
x_1134 = x_1189;
x_1135 = x_1190;
x_1136 = x_1297;
x_1137 = x_1191;
x_1138 = x_1192;
x_1139 = x_1193;
x_1140 = x_1194;
x_1141 = x_1195;
x_1142 = x_1196;
x_1143 = x_1197;
x_1144 = x_1198;
x_1145 = x_1306;
goto block_1172;
}
else
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1307 = lean_ctor_get(x_1294, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1294, 1);
lean_inc(x_1308);
if (lean_is_exclusive(x_1294)) {
 lean_ctor_release(x_1294, 0);
 lean_ctor_release(x_1294, 1);
 x_1309 = x_1294;
} else {
 lean_dec_ref(x_1294);
 x_1309 = lean_box(0);
}
if (lean_is_scalar(x_1309)) {
 x_1310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1310 = x_1309;
}
lean_ctor_set(x_1310, 0, x_1307);
lean_ctor_set(x_1310, 1, x_1308);
return x_1310;
}
}
else
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1131);
x_1311 = lean_ctor_get(x_1289, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1289, 1);
lean_inc(x_1312);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 lean_ctor_release(x_1289, 1);
 x_1313 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1313)) {
 x_1314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1314 = x_1313;
}
lean_ctor_set(x_1314, 0, x_1311);
lean_ctor_set(x_1314, 1, x_1312);
return x_1314;
}
}
}
}
else
{
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
return x_1203;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1198);
lean_dec_ref(x_1197);
lean_dec(x_1196);
lean_dec_ref(x_1195);
lean_dec(x_1194);
lean_dec_ref(x_1193);
lean_dec(x_1192);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
x_1315 = lean_ctor_get(x_1200, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1200, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_1200)) {
 lean_ctor_release(x_1200, 0);
 lean_ctor_release(x_1200, 1);
 x_1317 = x_1200;
} else {
 lean_dec_ref(x_1200);
 x_1317 = lean_box(0);
}
if (lean_is_scalar(x_1317)) {
 x_1318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1318 = x_1317;
}
lean_ctor_set(x_1318, 0, x_1315);
lean_ctor_set(x_1318, 1, x_1316);
return x_1318;
}
}
block_1418:
{
lean_object* x_1323; 
x_1323 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1186);
if (lean_obj_tag(x_1323) == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1324 = lean_ctor_get(x_1323, 0);
lean_inc(x_1324);
x_1325 = lean_ctor_get(x_1323, 1);
lean_inc(x_1325);
lean_dec_ref(x_1323);
x_1326 = lean_ctor_get(x_1324, 0);
lean_inc(x_1326);
lean_dec(x_1324);
x_1327 = l_Lean_Meta_Grind_SplitInfo_source(x_1124);
lean_inc(x_1327);
lean_inc(x_1322);
lean_inc_ref(x_1131);
x_1328 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_1328, 0, x_1131);
lean_closure_set(x_1328, 1, x_1322);
lean_closure_set(x_1328, 2, x_1125);
lean_closure_set(x_1328, 3, x_1327);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1329 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1326, x_1328, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1325);
if (lean_obj_tag(x_1329) == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1329, 1);
lean_inc(x_1331);
lean_dec_ref(x_1329);
x_1332 = lean_ctor_get(x_1330, 1);
lean_inc(x_1332);
lean_dec(x_1330);
x_1333 = lean_st_ref_take(x_3, x_1331);
x_1334 = lean_ctor_get(x_1333, 0);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1333, 1);
lean_inc(x_1335);
lean_dec_ref(x_1333);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
if (lean_is_exclusive(x_1334)) {
 lean_ctor_release(x_1334, 0);
 lean_ctor_release(x_1334, 1);
 x_1337 = x_1334;
} else {
 lean_dec_ref(x_1334);
 x_1337 = lean_box(0);
}
if (lean_is_scalar(x_1337)) {
 x_1338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1338 = x_1337;
}
lean_ctor_set(x_1338, 0, x_1332);
lean_ctor_set(x_1338, 1, x_1336);
x_1339 = lean_st_ref_set(x_3, x_1338, x_1335);
x_1340 = lean_ctor_get(x_1339, 1);
lean_inc(x_1340);
lean_dec_ref(x_1339);
x_1341 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1340);
if (lean_obj_tag(x_1341) == 0)
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; 
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1341, 1);
lean_inc(x_1343);
lean_dec_ref(x_1341);
x_1344 = lean_ctor_get(x_1342, 0);
lean_inc(x_1344);
lean_dec(x_1342);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1345 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1344, x_1320, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1343);
if (lean_obj_tag(x_1345) == 0)
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1346 = lean_ctor_get(x_1345, 0);
lean_inc(x_1346);
x_1347 = lean_ctor_get(x_1345, 1);
lean_inc(x_1347);
lean_dec_ref(x_1345);
x_1348 = lean_ctor_get(x_1346, 1);
lean_inc(x_1348);
lean_dec(x_1346);
x_1349 = lean_st_ref_take(x_3, x_1347);
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec_ref(x_1349);
x_1352 = lean_ctor_get(x_1350, 1);
lean_inc(x_1352);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 lean_ctor_release(x_1350, 1);
 x_1353 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1353 = lean_box(0);
}
if (lean_is_scalar(x_1353)) {
 x_1354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1354 = x_1353;
}
lean_ctor_set(x_1354, 0, x_1348);
lean_ctor_set(x_1354, 1, x_1352);
x_1355 = lean_st_ref_set(x_3, x_1354, x_1351);
x_1356 = lean_ctor_get(x_1355, 1);
lean_inc(x_1356);
lean_dec_ref(x_1355);
x_1357 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1358 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3(x_1357, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1356);
if (lean_obj_tag(x_1358) == 0)
{
lean_object* x_1359; uint8_t x_1360; 
x_1359 = lean_ctor_get(x_1358, 0);
lean_inc(x_1359);
x_1360 = lean_unbox(x_1359);
lean_dec(x_1359);
if (x_1360 == 0)
{
lean_object* x_1361; 
lean_dec(x_1177);
lean_dec_ref(x_2);
x_1361 = lean_ctor_get(x_1358, 1);
lean_inc(x_1361);
lean_dec_ref(x_1358);
x_1188 = x_1327;
x_1189 = x_1321;
x_1190 = x_1322;
x_1191 = x_3;
x_1192 = x_4;
x_1193 = x_5;
x_1194 = x_6;
x_1195 = x_7;
x_1196 = x_8;
x_1197 = x_9;
x_1198 = x_10;
x_1199 = x_1361;
goto block_1319;
}
else
{
lean_object* x_1362; lean_object* x_1363; 
x_1362 = lean_ctor_get(x_1358, 1);
lean_inc(x_1362);
lean_dec_ref(x_1358);
x_1363 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1362);
if (lean_obj_tag(x_1363) == 0)
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1364 = lean_ctor_get(x_1363, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1363, 1);
lean_inc(x_1365);
lean_dec_ref(x_1363);
x_1366 = lean_ctor_get(x_1364, 0);
lean_inc(x_1366);
lean_dec(x_1364);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1367 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_1366, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1365);
if (lean_obj_tag(x_1367) == 0)
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1368 = lean_ctor_get(x_1367, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1367, 1);
lean_inc(x_1369);
lean_dec_ref(x_1367);
x_1370 = lean_ctor_get(x_1368, 1);
lean_inc(x_1370);
lean_dec(x_1368);
x_1371 = lean_st_ref_take(x_3, x_1369);
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
if (lean_is_exclusive(x_1371)) {
 lean_ctor_release(x_1371, 0);
 lean_ctor_release(x_1371, 1);
 x_1374 = x_1371;
} else {
 lean_dec_ref(x_1371);
 x_1374 = lean_box(0);
}
x_1375 = lean_ctor_get(x_1372, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1372)) {
 lean_ctor_release(x_1372, 0);
 lean_ctor_release(x_1372, 1);
 x_1376 = x_1372;
} else {
 lean_dec_ref(x_1372);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_1370);
lean_ctor_set(x_1377, 1, x_1375);
x_1378 = lean_st_ref_set(x_3, x_1377, x_1373);
x_1379 = lean_ctor_get(x_1378, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1378)) {
 lean_ctor_release(x_1378, 0);
 lean_ctor_release(x_1378, 1);
 x_1380 = x_1378;
} else {
 lean_dec_ref(x_1378);
 x_1380 = lean_box(0);
}
lean_inc_ref(x_1131);
x_1381 = l_Lean_MessageData_ofExpr(x_1131);
x_1382 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_1380)) {
 x_1383 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1383 = x_1380;
 lean_ctor_set_tag(x_1383, 7);
}
lean_ctor_set(x_1383, 0, x_1381);
lean_ctor_set(x_1383, 1, x_1382);
x_1384 = l_Nat_reprFast(x_1177);
x_1385 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1385, 0, x_1384);
x_1386 = l_Lean_MessageData_ofFormat(x_1385);
if (lean_is_scalar(x_1374)) {
 x_1387 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1387 = x_1374;
 lean_ctor_set_tag(x_1387, 7);
}
lean_ctor_set(x_1387, 0, x_1383);
lean_ctor_set(x_1387, 1, x_1386);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1388 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4(x_1357, x_1387, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1379);
if (lean_obj_tag(x_1388) == 0)
{
lean_object* x_1389; 
x_1389 = lean_ctor_get(x_1388, 1);
lean_inc(x_1389);
lean_dec_ref(x_1388);
x_1188 = x_1327;
x_1189 = x_1321;
x_1190 = x_1322;
x_1191 = x_3;
x_1192 = x_4;
x_1193 = x_5;
x_1194 = x_6;
x_1195 = x_7;
x_1196 = x_8;
x_1197 = x_9;
x_1198 = x_10;
x_1199 = x_1389;
goto block_1319;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1187);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1390 = lean_ctor_get(x_1388, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1388, 1);
lean_inc(x_1391);
if (lean_is_exclusive(x_1388)) {
 lean_ctor_release(x_1388, 0);
 lean_ctor_release(x_1388, 1);
 x_1392 = x_1388;
} else {
 lean_dec_ref(x_1388);
 x_1392 = lean_box(0);
}
if (lean_is_scalar(x_1392)) {
 x_1393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1393 = x_1392;
}
lean_ctor_set(x_1393, 0, x_1390);
lean_ctor_set(x_1393, 1, x_1391);
return x_1393;
}
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1394 = lean_ctor_get(x_1367, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1367, 1);
lean_inc(x_1395);
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 lean_ctor_release(x_1367, 1);
 x_1396 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1396 = lean_box(0);
}
if (lean_is_scalar(x_1396)) {
 x_1397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1397 = x_1396;
}
lean_ctor_set(x_1397, 0, x_1394);
lean_ctor_set(x_1397, 1, x_1395);
return x_1397;
}
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1398 = lean_ctor_get(x_1363, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1363, 1);
lean_inc(x_1399);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1400 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1400 = lean_box(0);
}
if (lean_is_scalar(x_1400)) {
 x_1401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1401 = x_1400;
}
lean_ctor_set(x_1401, 0, x_1398);
lean_ctor_set(x_1401, 1, x_1399);
return x_1401;
}
}
}
else
{
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1358;
}
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1402 = lean_ctor_get(x_1345, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1345, 1);
lean_inc(x_1403);
if (lean_is_exclusive(x_1345)) {
 lean_ctor_release(x_1345, 0);
 lean_ctor_release(x_1345, 1);
 x_1404 = x_1345;
} else {
 lean_dec_ref(x_1345);
 x_1404 = lean_box(0);
}
if (lean_is_scalar(x_1404)) {
 x_1405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1405 = x_1404;
}
lean_ctor_set(x_1405, 0, x_1402);
lean_ctor_set(x_1405, 1, x_1403);
return x_1405;
}
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1320);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1406 = lean_ctor_get(x_1341, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1341, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1341)) {
 lean_ctor_release(x_1341, 0);
 lean_ctor_release(x_1341, 1);
 x_1408 = x_1341;
} else {
 lean_dec_ref(x_1341);
 x_1408 = lean_box(0);
}
if (lean_is_scalar(x_1408)) {
 x_1409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1409 = x_1408;
}
lean_ctor_set(x_1409, 0, x_1406);
lean_ctor_set(x_1409, 1, x_1407);
return x_1409;
}
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
lean_dec(x_1327);
lean_dec(x_1322);
lean_dec_ref(x_1320);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1410 = lean_ctor_get(x_1329, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1329, 1);
lean_inc(x_1411);
if (lean_is_exclusive(x_1329)) {
 lean_ctor_release(x_1329, 0);
 lean_ctor_release(x_1329, 1);
 x_1412 = x_1329;
} else {
 lean_dec_ref(x_1329);
 x_1412 = lean_box(0);
}
if (lean_is_scalar(x_1412)) {
 x_1413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1413 = x_1412;
}
lean_ctor_set(x_1413, 0, x_1410);
lean_ctor_set(x_1413, 1, x_1411);
return x_1413;
}
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
lean_dec(x_1322);
lean_dec_ref(x_1320);
lean_dec_ref(x_1187);
lean_dec(x_1177);
lean_dec_ref(x_1131);
lean_dec(x_1125);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1414 = lean_ctor_get(x_1323, 0);
lean_inc(x_1414);
x_1415 = lean_ctor_get(x_1323, 1);
lean_inc(x_1415);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1416 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1416 = lean_box(0);
}
if (lean_is_scalar(x_1416)) {
 x_1417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1417 = x_1416;
}
lean_ctor_set(x_1417, 0, x_1414);
lean_ctor_set(x_1417, 1, x_1415);
return x_1417;
}
}
block_1423:
{
uint8_t x_1421; 
x_1421 = 1;
if (x_1420 == 0)
{
lean_inc(x_1177);
x_1321 = x_1421;
x_1322 = x_1177;
goto block_1418;
}
else
{
lean_object* x_1422; 
x_1422 = lean_nat_add(x_1177, x_1419);
x_1321 = x_1421;
x_1322 = x_1422;
goto block_1418;
}
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
lean_dec_ref(x_1131);
lean_dec(x_1125);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1425 = lean_ctor_get(x_1174, 0);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_1174, 1);
lean_inc(x_1426);
if (lean_is_exclusive(x_1174)) {
 lean_ctor_release(x_1174, 0);
 lean_ctor_release(x_1174, 1);
 x_1427 = x_1174;
} else {
 lean_dec_ref(x_1174);
 x_1427 = lean_box(0);
}
if (lean_is_scalar(x_1427)) {
 x_1428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1428 = x_1427;
}
lean_ctor_set(x_1428, 0, x_1425);
lean_ctor_set(x_1428, 1, x_1426);
return x_1428;
}
block_1172:
{
lean_object* x_1146; 
x_1146 = l_Lean_Meta_Grind_getGoal___redArg(x_1137, x_1145);
if (lean_obj_tag(x_1146) == 0)
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1146, 1);
lean_inc(x_1148);
lean_dec_ref(x_1146);
x_1149 = l_List_lengthTR___redArg(x_1136);
x_1150 = l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
x_1151 = l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__1(x_1147, x_1131, x_1149, x_1133, x_1136, x_1150);
x_1152 = l_Lean_mkMVar(x_1132);
lean_inc(x_1144);
lean_inc_ref(x_1143);
lean_inc(x_1142);
lean_inc_ref(x_1141);
lean_inc(x_1140);
lean_inc_ref(x_1139);
lean_inc(x_1138);
lean_inc(x_1137);
lean_inc(x_1135);
x_1153 = l_Lean_Meta_Grind_mkChoice(x_1152, x_1151, x_1135, x_1137, x_1138, x_1139, x_1140, x_1141, x_1142, x_1143, x_1144, x_1148);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; lean_object* x_1155; 
x_1154 = lean_ctor_get(x_1153, 1);
lean_inc(x_1154);
lean_dec_ref(x_1153);
x_1155 = l_Lean_Meta_Grind_intros(x_1135, x_1137, x_1138, x_1139, x_1140, x_1141, x_1142, x_1143, x_1144, x_1154);
if (lean_obj_tag(x_1155) == 0)
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1156 = lean_ctor_get(x_1155, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1155)) {
 lean_ctor_release(x_1155, 0);
 lean_ctor_release(x_1155, 1);
 x_1157 = x_1155;
} else {
 lean_dec_ref(x_1155);
 x_1157 = lean_box(0);
}
x_1158 = lean_box(x_1134);
if (lean_is_scalar(x_1157)) {
 x_1159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1159 = x_1157;
}
lean_ctor_set(x_1159, 0, x_1158);
lean_ctor_set(x_1159, 1, x_1156);
return x_1159;
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1160 = lean_ctor_get(x_1155, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1155, 1);
lean_inc(x_1161);
if (lean_is_exclusive(x_1155)) {
 lean_ctor_release(x_1155, 0);
 lean_ctor_release(x_1155, 1);
 x_1162 = x_1155;
} else {
 lean_dec_ref(x_1155);
 x_1162 = lean_box(0);
}
if (lean_is_scalar(x_1162)) {
 x_1163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1163 = x_1162;
}
lean_ctor_set(x_1163, 0, x_1160);
lean_ctor_set(x_1163, 1, x_1161);
return x_1163;
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
lean_dec(x_1144);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec_ref(x_1141);
lean_dec(x_1140);
lean_dec_ref(x_1139);
lean_dec(x_1138);
lean_dec(x_1137);
lean_dec(x_1135);
x_1164 = lean_ctor_get(x_1153, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1153, 1);
lean_inc(x_1165);
if (lean_is_exclusive(x_1153)) {
 lean_ctor_release(x_1153, 0);
 lean_ctor_release(x_1153, 1);
 x_1166 = x_1153;
} else {
 lean_dec_ref(x_1153);
 x_1166 = lean_box(0);
}
if (lean_is_scalar(x_1166)) {
 x_1167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1167 = x_1166;
}
lean_ctor_set(x_1167, 0, x_1164);
lean_ctor_set(x_1167, 1, x_1165);
return x_1167;
}
}
else
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
lean_dec(x_1144);
lean_dec_ref(x_1143);
lean_dec(x_1142);
lean_dec_ref(x_1141);
lean_dec(x_1140);
lean_dec_ref(x_1139);
lean_dec(x_1138);
lean_dec(x_1137);
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1133);
lean_dec(x_1132);
lean_dec_ref(x_1131);
x_1168 = lean_ctor_get(x_1146, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1146, 1);
lean_inc(x_1169);
if (lean_is_exclusive(x_1146)) {
 lean_ctor_release(x_1146, 0);
 lean_ctor_release(x_1146, 1);
 x_1170 = x_1146;
} else {
 lean_dec_ref(x_1146);
 x_1170 = lean_box(0);
}
if (lean_is_scalar(x_1170)) {
 x_1171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1171 = x_1170;
}
lean_ctor_set(x_1171, 0, x_1168);
lean_ctor_set(x_1171, 1, x_1169);
return x_1171;
}
}
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
lean_dec(x_1125);
lean_dec_ref(x_1124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1429 = lean_ctor_get(x_1127, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1127, 1);
lean_inc(x_1430);
if (lean_is_exclusive(x_1127)) {
 lean_ctor_release(x_1127, 0);
 lean_ctor_release(x_1127, 1);
 x_1431 = x_1127;
} else {
 lean_dec_ref(x_1127);
 x_1431 = lean_box(0);
}
if (lean_is_scalar(x_1431)) {
 x_1432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1432 = x_1431;
}
lean_ctor_set(x_1432, 0, x_1429);
lean_ctor_set(x_1432, 1, x_1430);
return x_1432;
}
}
}
}
else
{
uint8_t x_1433; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1433 = !lean_is_exclusive(x_16);
if (x_1433 == 0)
{
return x_16;
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1434 = lean_ctor_get(x_16, 0);
x_1435 = lean_ctor_get(x_16, 1);
lean_inc(x_1435);
lean_inc(x_1434);
lean_dec(x_16);
x_1436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1436, 0, x_1434);
lean_ctor_set(x_1436, 1, x_1435);
return x_1436;
}
}
}
else
{
uint8_t x_1437; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_1437 = !lean_is_exclusive(x_12);
if (x_1437 == 0)
{
return x_12;
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1438 = lean_ctor_get(x_12, 0);
x_1439 = lean_ctor_get(x_12, 1);
lean_inc(x_1439);
lean_inc(x_1438);
lean_dec(x_12);
x_1440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1440, 0, x_1438);
lean_ctor_set(x_1440, 1, x_1439);
return x_1440;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__0___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__1___boxed), 9, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__9), 11, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_splitNext_spec__0___redArg(x_13, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__3___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__4___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_splitNext___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_splitNext___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_splitNext___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_splitNext___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_splitNext___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SearchM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedSplitStatus_default = _init_l_Lean_Meta_Grind_instInhabitedSplitStatus_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSplitStatus_default);
l_Lean_Meta_Grind_instInhabitedSplitStatus = _init_l_Lean_Meta_Grind_instInhabitedSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSplitStatus);
l_Lean_Meta_Grind_instBEqSplitStatus___closed__0 = _init_l_Lean_Meta_Grind_instBEqSplitStatus___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqSplitStatus___closed__0);
l_Lean_Meta_Grind_instBEqSplitStatus = _init_l_Lean_Meta_Grind_instBEqSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqSplitStatus);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__0);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__2);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__6);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__7);
l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8 = _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8);
l_Lean_Meta_Grind_instReprSplitStatus___closed__0 = _init_l_Lean_Meta_Grind_instReprSplitStatus___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus___closed__0);
l_Lean_Meta_Grind_instReprSplitStatus = _init_l_Lean_Meta_Grind_instReprSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__17 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__17();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__17);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__18);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__19 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__19();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__19);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0_spec__0_spec__0___closed__20);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__0);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__1);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__2);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__3 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__0___redArg___closed__3);
l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0 = _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__0();
l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1 = _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__1);
l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2 = _init_l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__9___redArg___closed__2);
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
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13);
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
