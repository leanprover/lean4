// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Basic
// Imports: Lean.Meta.Reduce Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Basic Lean.Elab.Tactic.BuiltinTactic
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__3;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__4;
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_closeMainGoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_Conv_evalSepByIndentConv___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__7;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Conv_getLhsRhsCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_Conv_evalSepByIndentConv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4;
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18;
static lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__2;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__4;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__4;
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6;
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___closed__1;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__3;
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Conv_getLhsRhsCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8;
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__2;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__4;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1;
lean_object* l_Lean_Elab_Tactic_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__5;
lean_object* l_Lean_Meta_zetaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1;
lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2;
lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__3;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__3;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_zetaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__4;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__5;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__19;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__4;
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__6;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__1;
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__6;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__5;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__7;
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__5;
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2;
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__16;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__3;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__5;
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkLHSGoalRaw(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_mkLHSGoalRaw(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
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
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_mkLHSGoalRaw(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_3);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_16);
x_18 = l_Lean_Meta_mkEq(x_1, x_16, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkLHSGoalRaw(x_19);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_21, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_22, 0, x_14);
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
lean_ctor_set(x_14, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_14);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
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
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_32);
x_34 = l_Lean_Meta_mkEq(x_1, x_32, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkLHSGoalRaw(x_35);
x_38 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_37, x_2, x_3, x_4, x_5, x_6, x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_ctor_set(x_42, 0, x_32);
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
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_46 = x_34;
} else {
 lean_dec_ref(x_34);
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
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Elab_Tactic_Conv_mkLHSGoal(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_12, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_isLHSGoal_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1(x_1, x_12, x_2, x_3, x_4, x_5, x_10);
return x_13;
}
else
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_isLHSGoal_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1(x_1, x_17, x_2, x_3, x_4, x_5, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_Conv_markAsConvGoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_20 = l_Lean_Meta_saveState___rarg(x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_23 = l_Lean_MVarId_refl(x_13, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_13);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
x_15 = x_25;
x_16 = x_24;
goto block_19;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
x_29 = l_Lean_Exception_isInterrupt(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_23);
lean_dec(x_27);
x_31 = l_Lean_Meta_SavedState_restore(x_21, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_21);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Meta_saveState___rarg(x_8, x_9, x_10, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_MVarId_inferInstance(x_13, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
x_15 = x_38;
x_16 = x_37;
goto block_19;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
x_42 = l_Lean_Exception_isInterrupt(x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_36);
lean_dec(x_40);
x_44 = l_Lean_Meta_SavedState_restore(x_34, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_34);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
x_15 = x_46;
x_16 = x_45;
goto block_19;
}
else
{
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_36;
}
}
else
{
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_36;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = l_Lean_Exception_isInterrupt(x_47);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Exception_isRuntime(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_47);
x_51 = l_Lean_Meta_SavedState_restore(x_34, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_34);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
x_15 = x_53;
x_16 = x_52;
goto block_19;
}
else
{
lean_object* x_54; 
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_23;
}
}
else
{
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_23;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_23, 0);
x_57 = lean_ctor_get(x_23, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_23);
x_58 = l_Lean_Exception_isInterrupt(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Exception_isRuntime(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_56);
x_60 = l_Lean_Meta_SavedState_restore(x_21, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_21);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Meta_saveState___rarg(x_8, x_9, x_10, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_MVarId_inferInstance(x_13, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
x_15 = x_67;
x_16 = x_66;
goto block_19;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Exception_isInterrupt(x_68);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = l_Lean_Exception_isRuntime(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_68);
x_73 = l_Lean_Meta_SavedState_restore(x_63, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_63);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1;
x_15 = x_75;
x_16 = x_74;
goto block_19;
}
else
{
lean_object* x_76; 
lean_dec(x_63);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec(x_63);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_56);
lean_ctor_set(x_78, 1, x_57);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_56);
lean_ctor_set(x_79, 1, x_57);
return x_79;
}
}
}
block_19:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_1 = x_14;
x_2 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_convert___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("convert tactic failed, there are unsolved goals\n", 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_convert___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_convert___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
x_19 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_41; lean_object* x_42; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Expr_mvarId_x21(x_17);
x_24 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_24);
lean_ctor_set(x_19, 0, x_23);
x_49 = l_Lean_Elab_Tactic_setGoals(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1(x_54, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = l_Lean_Elab_Tactic_Conv_convert___closed__1;
x_66 = l_List_isEmpty___rarg(x_63);
lean_dec(x_63);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_67 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = l_Lean_Elab_goalsToMessageData(x_69);
x_72 = l_Lean_Elab_Tactic_Conv_convert___closed__3;
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_71);
lean_ctor_set(x_67, 0, x_72);
x_73 = l_Lean_Elab_Tactic_Conv_convert___closed__5;
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_67);
x_74 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_41 = x_75;
x_42 = x_76;
goto block_48;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_67, 0);
x_78 = lean_ctor_get(x_67, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_67);
x_79 = l_Lean_Elab_goalsToMessageData(x_77);
x_80 = l_Lean_Elab_Tactic_Conv_convert___closed__3;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_Tactic_Conv_convert___closed__5;
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_82);
lean_ctor_set(x_61, 0, x_81);
x_83 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_41 = x_84;
x_42 = x_85;
goto block_48;
}
}
else
{
lean_object* x_86; 
lean_free_object(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_86 = lean_apply_10(x_65, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_25 = x_87;
x_26 = x_88;
goto block_40;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_41 = x_89;
x_42 = x_90;
goto block_48;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_61, 0);
x_92 = lean_ctor_get(x_61, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_61);
x_93 = l_Lean_Elab_Tactic_Conv_convert___closed__1;
x_94 = l_List_isEmpty___rarg(x_91);
lean_dec(x_91);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_95 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_92);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Elab_goalsToMessageData(x_96);
x_100 = l_Lean_Elab_Tactic_Conv_convert___closed__3;
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_101 = x_98;
 lean_ctor_set_tag(x_101, 7);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Elab_Tactic_Conv_convert___closed__5;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_97);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_41 = x_105;
x_42 = x_106;
goto block_48;
}
else
{
lean_object* x_107; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = lean_apply_10(x_93, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_92);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_25 = x_108;
x_26 = x_109;
goto block_40;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_41 = x_110;
x_42 = x_111;
goto block_48;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_112 = lean_ctor_get(x_57, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_57, 1);
lean_inc(x_113);
lean_dec(x_57);
x_41 = x_112;
x_42 = x_113;
goto block_48;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_114 = lean_ctor_get(x_51, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_51, 1);
lean_inc(x_115);
lean_dec(x_51);
x_41 = x_114;
x_42 = x_115;
goto block_48;
}
block_40:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_25);
x_27 = l_Lean_Elab_Tactic_setGoals(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
if (lean_is_scalar(x_18)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_18;
}
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
if (lean_is_scalar(x_18)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_18;
}
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
block_48:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Elab_Tactic_setGoals(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_135; lean_object* x_136; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_116 = lean_ctor_get(x_19, 0);
x_117 = lean_ctor_get(x_19, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_19);
x_118 = l_Lean_Expr_mvarId_x21(x_17);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_142 = l_Lean_Elab_Tactic_setGoals(x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_117);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_144 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_150 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1(x_147, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_151);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = l_Lean_Elab_Tactic_Conv_convert___closed__1;
x_159 = l_List_isEmpty___rarg(x_155);
lean_dec(x_155);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_160 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_156);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = l_Lean_Elab_goalsToMessageData(x_161);
x_165 = l_Lean_Elab_Tactic_Conv_convert___closed__3;
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(7, 2, 0);
} else {
 x_166 = x_163;
 lean_ctor_set_tag(x_166, 7);
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Elab_Tactic_Conv_convert___closed__5;
if (lean_is_scalar(x_157)) {
 x_168 = lean_alloc_ctor(7, 2, 0);
} else {
 x_168 = x_157;
 lean_ctor_set_tag(x_168, 7);
}
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_168, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_162);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_135 = x_170;
x_136 = x_171;
goto block_141;
}
else
{
lean_object* x_172; 
lean_dec(x_157);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_172 = lean_apply_10(x_158, x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_156);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_121 = x_173;
x_122 = x_174;
goto block_134;
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_176;
goto block_141;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_177 = lean_ctor_get(x_150, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_150, 1);
lean_inc(x_178);
lean_dec(x_150);
x_135 = x_177;
x_136 = x_178;
goto block_141;
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_179 = lean_ctor_get(x_144, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_144, 1);
lean_inc(x_180);
lean_dec(x_144);
x_135 = x_179;
x_136 = x_180;
goto block_141;
}
block_134:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_121);
x_123 = l_Lean_Elab_Tactic_setGoals(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_127);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_18;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_129);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
block_141:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = l_Lean_Elab_Tactic_setGoals(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_136);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_13);
if (x_181 == 0)
{
return x_13;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_13, 0);
x_183 = lean_ctor_get(x_13, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_13);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_convert___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Conv_getLhsRhsCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
static lean_object* _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'conv' goal", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_matchEq_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__2;
x_14 = l_Lean_throwError___at_Lean_Elab_Tactic_Conv_getLhsRhsCore___spec__1(x_13, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_26 = x_16;
} else {
 lean_dec_ref(x_16);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Conv_getLhsRhsCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_Tactic_Conv_getLhsRhsCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_getLhsRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_getLhsRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_getLhsRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Conv_getRhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_Tactic_Conv_getRhs(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_mkEq(x_1, x_16, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_13);
x_21 = l_Lean_MVarId_getTag(x_13, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkLHSGoalRaw(x_19);
lean_inc(x_7);
x_25 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_24, x_22, x_7, x_8, x_9, x_10, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_26);
x_28 = l_Lean_Meta_mkEqTrans(x_2, x_26, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_MVarId_assign___at_Lean_Elab_Tactic_closeMainGoal___spec__1(x_13, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_36 = lean_box(0);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_36);
lean_ctor_set(x_31, 0, x_35);
x_37 = l_Lean_Elab_Tactic_replaceMainGoal(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Tactic_replaceMainGoal(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
return x_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_12);
if (x_59 == 0)
{
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_12, 0);
x_61 = lean_ctor_get(x_12, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_12);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_updateLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkLHSGoalRaw(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_MVarId_replaceTargetDefEq(x_13, x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_replaceMainGoal(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Tactic_Conv_getRhs(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_changeLhs___lambda__1___boxed), 11, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_changeLhs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_whnf(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_Conv_changeLhs(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalWhnf(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Conv", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("whnf", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalWhnf", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__11;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(91u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(34u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(89u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(59u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_reduce(x_11, x_13, x_13, x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_Conv_changeLhs(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalReduce___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___rarg___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_Conv_evalReduce___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalReduce(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduce", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalReduce", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(93u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(95u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(93u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(93u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(63u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Tactic_Conv_getLhs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__1;
x_14 = l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__2;
x_15 = 1;
x_16 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_11, x_13, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Tactic_Conv_changeLhs(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalZeta___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_Conv_evalZeta___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Conv_evalZeta(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zeta", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalZeta", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(97u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(99u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(40u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(97u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(97u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(59u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_Conv_evalSepByIndentConv___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_uget(x_1, x_3);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_4, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 0);
lean_dec(x_25);
x_26 = lean_nat_add(x_17, x_19);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_nat_mod(x_17, x_27);
lean_dec(x_17);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Lean_Elab_Tactic_saveTacticInfoForToken(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; size_t x_33; size_t x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
x_13 = x_32;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Lean_Elab_Tactic_evalTactic(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = 1;
x_43 = lean_usize_add(x_3, x_42);
x_3 = x_43;
x_13 = x_41;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_4);
x_49 = lean_nat_add(x_17, x_19);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_18);
lean_ctor_set(x_50, 2, x_19);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_mod(x_17, x_51);
lean_dec(x_17);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Lean_Elab_Tactic_saveTacticInfoForToken(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; size_t x_57; size_t x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_3 = x_58;
x_4 = x_50;
x_13 = x_56;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_50);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l_Lean_Elab_Tactic_evalTactic(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; size_t x_66; size_t x_67; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = 1;
x_67 = lean_usize_add(x_3, x_66);
x_3 = x_67;
x_4 = x_50;
x_13 = x_65;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_50);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_11 = l_Lean_Syntax_getArgs(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_array_get_size(x_11);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_Conv_evalSepByIndentConv___spec__1(x_11, x_17, x_18, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_Conv_evalSepByIndentConv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_Conv_evalSepByIndentConv___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("convSeq1Indented", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalConvSeq1Indented", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(109u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(110u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(59u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(28u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(109u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(109u);
x_2 = lean_unsigned_to_nat(83u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(63u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(83u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("allGoals", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("all_goals", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticTry_", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("try", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withReducible", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with_reducible", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticRfl", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__19;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rfl", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__11(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_3, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_10, 5);
lean_inc(x_19);
x_20 = 0;
x_21 = l_Lean_SourceInfo_fromRef(x_19, x_20);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_11, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3;
lean_inc(x_21);
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_21);
x_27 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12;
lean_inc(x_21);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15;
lean_inc(x_21);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18;
lean_inc(x_21);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21;
lean_inc(x_21);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20;
lean_inc(x_21);
x_36 = l_Lean_Syntax_node1(x_21, x_35, x_34);
x_37 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
lean_inc(x_21);
x_38 = l_Lean_Syntax_node1(x_21, x_37, x_36);
x_39 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7;
lean_inc(x_21);
x_40 = l_Lean_Syntax_node1(x_21, x_39, x_38);
x_41 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5;
lean_inc(x_21);
x_42 = l_Lean_Syntax_node1(x_21, x_41, x_40);
x_43 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17;
lean_inc(x_21);
x_44 = l_Lean_Syntax_node2(x_21, x_43, x_32, x_42);
lean_inc(x_21);
x_45 = l_Lean_Syntax_node1(x_21, x_37, x_44);
lean_inc(x_21);
x_46 = l_Lean_Syntax_node1(x_21, x_39, x_45);
lean_inc(x_21);
x_47 = l_Lean_Syntax_node1(x_21, x_41, x_46);
x_48 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14;
lean_inc(x_21);
x_49 = l_Lean_Syntax_node2(x_21, x_48, x_30, x_47);
lean_inc(x_21);
x_50 = l_Lean_Syntax_node1(x_21, x_37, x_49);
lean_inc(x_21);
x_51 = l_Lean_Syntax_node1(x_21, x_39, x_50);
lean_inc(x_21);
x_52 = l_Lean_Syntax_node1(x_21, x_41, x_51);
x_53 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22;
lean_inc(x_21);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_21);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11;
lean_inc(x_21);
x_56 = l_Lean_Syntax_node3(x_21, x_55, x_28, x_52, x_54);
lean_inc(x_21);
x_57 = l_Lean_Syntax_node1(x_21, x_37, x_56);
lean_inc(x_21);
x_58 = l_Lean_Syntax_node1(x_21, x_39, x_57);
lean_inc(x_21);
x_59 = l_Lean_Syntax_node1(x_21, x_41, x_58);
x_60 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2;
x_61 = l_Lean_Syntax_node2(x_21, x_60, x_22, x_59);
x_62 = l_Lean_Elab_Tactic_evalTactic(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_63 = lean_ctor_get(x_22, 1);
lean_inc(x_63);
lean_dec(x_22);
x_64 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3;
lean_inc(x_21);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12;
lean_inc(x_21);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_21);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15;
lean_inc(x_21);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_21);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18;
lean_inc(x_21);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_21);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21;
lean_inc(x_21);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_21);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20;
lean_inc(x_21);
x_75 = l_Lean_Syntax_node1(x_21, x_74, x_73);
x_76 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
lean_inc(x_21);
x_77 = l_Lean_Syntax_node1(x_21, x_76, x_75);
x_78 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7;
lean_inc(x_21);
x_79 = l_Lean_Syntax_node1(x_21, x_78, x_77);
x_80 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5;
lean_inc(x_21);
x_81 = l_Lean_Syntax_node1(x_21, x_80, x_79);
x_82 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17;
lean_inc(x_21);
x_83 = l_Lean_Syntax_node2(x_21, x_82, x_71, x_81);
lean_inc(x_21);
x_84 = l_Lean_Syntax_node1(x_21, x_76, x_83);
lean_inc(x_21);
x_85 = l_Lean_Syntax_node1(x_21, x_78, x_84);
lean_inc(x_21);
x_86 = l_Lean_Syntax_node1(x_21, x_80, x_85);
x_87 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14;
lean_inc(x_21);
x_88 = l_Lean_Syntax_node2(x_21, x_87, x_69, x_86);
lean_inc(x_21);
x_89 = l_Lean_Syntax_node1(x_21, x_76, x_88);
lean_inc(x_21);
x_90 = l_Lean_Syntax_node1(x_21, x_78, x_89);
lean_inc(x_21);
x_91 = l_Lean_Syntax_node1(x_21, x_80, x_90);
x_92 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22;
lean_inc(x_21);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_21);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11;
lean_inc(x_21);
x_95 = l_Lean_Syntax_node3(x_21, x_94, x_67, x_91, x_93);
lean_inc(x_21);
x_96 = l_Lean_Syntax_node1(x_21, x_76, x_95);
lean_inc(x_21);
x_97 = l_Lean_Syntax_node1(x_21, x_78, x_96);
lean_inc(x_21);
x_98 = l_Lean_Syntax_node1(x_21, x_80, x_97);
x_99 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2;
x_100 = l_Lean_Syntax_node2(x_21, x_99, x_65, x_98);
x_101 = l_Lean_Elab_Tactic_evalTactic(x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = !lean_is_exclusive(x_17);
if (x_102 == 0)
{
return x_17;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_17, 0);
x_104 = lean_ctor_get(x_17, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_17);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = !lean_is_exclusive(x_13);
if (x_106 == 0)
{
return x_13;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_13, 0);
x_108 = lean_ctor_get(x_13, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_13);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed), 10, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__1), 11, 1);
lean_closure_set(x_18, 0, x_14);
x_19 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__1;
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___boxed), 12, 3);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 5);
x_23 = l_Lean_replaceRef(x_17, x_22);
lean_dec(x_22);
lean_dec(x_17);
lean_ctor_set(x_8, 5, x_23);
x_24 = l_Lean_Elab_Tactic_closeUsingOrAdmit(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
x_29 = lean_ctor_get(x_8, 4);
x_30 = lean_ctor_get(x_8, 5);
x_31 = lean_ctor_get(x_8, 6);
x_32 = lean_ctor_get(x_8, 7);
x_33 = lean_ctor_get(x_8, 8);
x_34 = lean_ctor_get(x_8, 9);
x_35 = lean_ctor_get(x_8, 10);
x_36 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_37 = lean_ctor_get(x_8, 11);
x_38 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_39 = l_Lean_replaceRef(x_17, x_30);
lean_dec(x_30);
lean_dec(x_17);
x_40 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_26);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_29);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_31);
lean_ctor_set(x_40, 7, x_32);
lean_ctor_set(x_40, 8, x_33);
lean_ctor_set(x_40, 9, x_34);
lean_ctor_set(x_40, 10, x_35);
lean_ctor_set(x_40, 11, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*12, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*12 + 1, x_38);
x_41 = l_Lean_Elab_Tactic_closeUsingOrAdmit(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_40, x_9, x_15);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("convSeqBracketed", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalConvSeqBracketed", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(112u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(118u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(59u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(64u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(112u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(112u);
x_2 = lean_unsigned_to_nat(83u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(63u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(83u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalNestedConv(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nestedConv", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalNestedConv", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(121u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(29u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(71u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(57u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(71u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalConvSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("convSeq", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalConvSeq", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(123u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(124u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(123u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(123u);
x_2 = lean_unsigned_to_nat(65u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(54u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(65u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Tactic_Conv_getLhs(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_15, x_16);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Tactic_Conv_convert(x_12, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Elab_Tactic_Conv_updateLhs(x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("convConvSeq", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalConvConvSeq", 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(126u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(129u);
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(54u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(26u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(126u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(126u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(58u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(73u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalParen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalParen", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalParen___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(131u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(132u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(131u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(131u);
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(52u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(61u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_getType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Lean_Meta_matchEq_x3f(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_Expr_getAppFn(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_isMVar(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_28; 
lean_free_object(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Elab_Tactic_Conv_mkLHSGoal(x_12, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_29, x_6, x_7, x_8, x_9, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = l_Lean_Expr_getAppFn(x_37);
lean_dec(x_37);
x_39 = l_Lean_Expr_isMVar(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Elab_Tactic_Conv_mkLHSGoal(x_12, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_42, x_6, x_7, x_8, x_9, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_List_reverse___rarg(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1___boxed), 10, 1);
lean_closure_set(x_17, 0, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_15, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_19);
{
lean_object* _tmp_0 = x_16;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_10 = x_20;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1___boxed), 10, 1);
lean_closure_set(x_28, 0, x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_26, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_2);
x_1 = x_27;
x_2 = x_32;
x_11 = x_31;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1(x_11, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_setGoals(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM_loop___at_Lean_Elab_Tactic_Conv_remarkAsConvGoal___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nestedTacticCore", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalNestedTacticCore", 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(147u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(149u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(59u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(34u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(147u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(147u);
x_2 = lean_unsigned_to_nat(83u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(63u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(83u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__1), 10, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Elab_Tactic_focus___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_mdataExpr_x21(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_MVarId_replaceTargetDefEq(x_12, x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_getMainTarget(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_isLHSGoal_x3f(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2(x_12, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__3___boxed), 10, 1);
lean_closure_set(x_19, 0, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_Elab_Tactic_withMainContext___rarg(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2(x_12, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalNestedTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nestedTactic", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalNestedTactic", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(151u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(157u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(55u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(43u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(151u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(151u);
x_2 = lean_unsigned_to_nat(75u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(59u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(75u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalConvTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("convTactic", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalConvTactic", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(159u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(160u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(159u);
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(159u);
x_2 = lean_unsigned_to_nat(71u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(57u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(71u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_MVarId_replaceTargetEq(x_13, x_1, x_2, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainTarget(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 5);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Tactic_Conv_convert(x_12, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1___boxed), 11, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Elab_Tactic_withMainContext___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Lean_SourceInfo_fromRef(x_14, x_26);
lean_dec(x_14);
x_28 = lean_st_ref_get(x_9, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15;
lean_inc(x_27);
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_32);
lean_ctor_set(x_28, 0, x_27);
x_33 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18;
lean_inc(x_27);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_27);
x_34 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21;
lean_inc(x_27);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20;
lean_inc(x_27);
x_37 = l_Lean_Syntax_node1(x_27, x_36, x_35);
x_38 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
lean_inc(x_27);
x_39 = l_Lean_Syntax_node1(x_27, x_38, x_37);
x_40 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7;
lean_inc(x_27);
x_41 = l_Lean_Syntax_node1(x_27, x_40, x_39);
x_42 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5;
lean_inc(x_27);
x_43 = l_Lean_Syntax_node1(x_27, x_42, x_41);
x_44 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17;
lean_inc(x_27);
x_45 = l_Lean_Syntax_node2(x_27, x_44, x_18, x_43);
lean_inc(x_27);
x_46 = l_Lean_Syntax_node1(x_27, x_38, x_45);
lean_inc(x_27);
x_47 = l_Lean_Syntax_node1(x_27, x_40, x_46);
lean_inc(x_27);
x_48 = l_Lean_Syntax_node1(x_27, x_42, x_47);
x_49 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14;
x_50 = l_Lean_Syntax_node2(x_27, x_49, x_28, x_48);
x_51 = l_Lean_Elab_Tactic_evalTactic(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_dec(x_28);
x_53 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15;
lean_inc(x_27);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_27);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18;
lean_inc(x_27);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_55);
lean_ctor_set(x_18, 0, x_27);
x_56 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21;
lean_inc(x_27);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_27);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20;
lean_inc(x_27);
x_59 = l_Lean_Syntax_node1(x_27, x_58, x_57);
x_60 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
lean_inc(x_27);
x_61 = l_Lean_Syntax_node1(x_27, x_60, x_59);
x_62 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7;
lean_inc(x_27);
x_63 = l_Lean_Syntax_node1(x_27, x_62, x_61);
x_64 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5;
lean_inc(x_27);
x_65 = l_Lean_Syntax_node1(x_27, x_64, x_63);
x_66 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17;
lean_inc(x_27);
x_67 = l_Lean_Syntax_node2(x_27, x_66, x_18, x_65);
lean_inc(x_27);
x_68 = l_Lean_Syntax_node1(x_27, x_60, x_67);
lean_inc(x_27);
x_69 = l_Lean_Syntax_node1(x_27, x_62, x_68);
lean_inc(x_27);
x_70 = l_Lean_Syntax_node1(x_27, x_64, x_69);
x_71 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14;
x_72 = l_Lean_Syntax_node2(x_27, x_71, x_54, x_70);
x_73 = l_Lean_Elab_Tactic_evalTactic(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_24);
if (x_74 == 0)
{
return x_24;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_24, 0);
x_76 = lean_ctor_get(x_24, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_24);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_18, 0);
x_79 = lean_ctor_get(x_18, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_18);
x_80 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1___boxed), 11, 2);
lean_closure_set(x_80, 0, x_78);
lean_closure_set(x_80, 1, x_79);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_Elab_Tactic_withMainContext___rarg(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = 0;
x_84 = l_Lean_SourceInfo_fromRef(x_14, x_83);
lean_dec(x_14);
x_85 = lean_st_ref_get(x_9, x_82);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15;
lean_inc(x_84);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(2, 2, 0);
} else {
 x_89 = x_87;
 lean_ctor_set_tag(x_89, 2);
}
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18;
lean_inc(x_84);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21;
lean_inc(x_84);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20;
lean_inc(x_84);
x_95 = l_Lean_Syntax_node1(x_84, x_94, x_93);
x_96 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
lean_inc(x_84);
x_97 = l_Lean_Syntax_node1(x_84, x_96, x_95);
x_98 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7;
lean_inc(x_84);
x_99 = l_Lean_Syntax_node1(x_84, x_98, x_97);
x_100 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5;
lean_inc(x_84);
x_101 = l_Lean_Syntax_node1(x_84, x_100, x_99);
x_102 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17;
lean_inc(x_84);
x_103 = l_Lean_Syntax_node2(x_84, x_102, x_91, x_101);
lean_inc(x_84);
x_104 = l_Lean_Syntax_node1(x_84, x_96, x_103);
lean_inc(x_84);
x_105 = l_Lean_Syntax_node1(x_84, x_98, x_104);
lean_inc(x_84);
x_106 = l_Lean_Syntax_node1(x_84, x_100, x_105);
x_107 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14;
x_108 = l_Lean_Syntax_node2(x_84, x_107, x_89, x_106);
x_109 = l_Lean_Elab_Tactic_evalTactic(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_81, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_81, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_112 = x_81;
} else {
 lean_dec_ref(x_81);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_11);
if (x_118 == 0)
{
return x_11;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_11, 0);
x_120 = lean_ctor_get(x_11, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_11);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__2), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_fvarId(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_14, x_16, x_2, x_3, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_replaceMainGoal(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_getLocalDeclFromUserName(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_9, 5);
lean_inc(x_15);
x_16 = l_Lean_LocalDecl_type(x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Tactic_Conv_convert(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__1___boxed), 12, 3);
lean_closure_set(x_24, 0, x_13);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_23);
x_25 = l_Lean_Elab_Tactic_withMainContext___rarg(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__2), 11, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
x_13 = l_Lean_Elab_Tactic_withMainContext___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("conv", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pattern", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(";", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("at", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
lean_inc(x_16);
x_18 = l_Lean_Syntax_matchesNull(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_matchesNull(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = l_Lean_Syntax_getArg(x_1, x_17);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__1;
x_26 = lean_array_push(x_25, x_2);
x_27 = lean_array_push(x_26, x_22);
x_28 = lean_box(2);
x_29 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_12, 5);
x_33 = l_Lean_replaceRef(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
lean_ctor_set(x_12, 5, x_33);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_34; 
x_34 = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(x_24, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
x_40 = lean_ctor_get(x_12, 2);
x_41 = lean_ctor_get(x_12, 3);
x_42 = lean_ctor_get(x_12, 4);
x_43 = lean_ctor_get(x_12, 5);
x_44 = lean_ctor_get(x_12, 6);
x_45 = lean_ctor_get(x_12, 7);
x_46 = lean_ctor_get(x_12, 8);
x_47 = lean_ctor_get(x_12, 9);
x_48 = lean_ctor_get(x_12, 10);
x_49 = lean_ctor_get_uint8(x_12, sizeof(void*)*12);
x_50 = lean_ctor_get(x_12, 11);
x_51 = lean_ctor_get_uint8(x_12, sizeof(void*)*12 + 1);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_52 = l_Lean_replaceRef(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
x_53 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_39);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_53, 6, x_44);
lean_ctor_set(x_53, 7, x_45);
lean_ctor_set(x_53, 8, x_46);
lean_ctor_set(x_53, 9, x_47);
lean_ctor_set(x_53, 10, x_48);
lean_ctor_set(x_53, 11, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*12, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*12 + 1, x_51);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_54; 
x_54 = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_53, x_13, x_14);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_55);
lean_dec(x_5);
x_56 = l_Lean_Syntax_getId(x_55);
lean_dec(x_55);
x_57 = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(x_24, x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_53, x_13, x_14);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_177; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = l_Lean_Syntax_getArg(x_16, x_58);
x_60 = l_Lean_Syntax_getArg(x_16, x_15);
lean_dec(x_16);
x_61 = l_Lean_Syntax_getArg(x_1, x_17);
x_62 = lean_unsigned_to_nat(4u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
x_177 = l_Lean_Syntax_getOptional_x3f(x_59);
lean_dec(x_59);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_box(0);
x_64 = x_178;
goto block_176;
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
x_64 = x_177;
goto block_176;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_64 = x_181;
goto block_176;
}
}
block_176:
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_12, 5);
lean_inc(x_65);
x_66 = 0;
x_67 = l_Lean_SourceInfo_fromRef(x_65, x_66);
lean_dec(x_65);
x_68 = lean_st_ref_get(x_13, x_14);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_70 = lean_ctor_get(x_68, 1);
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = 1;
x_73 = l_Lean_SourceInfo_fromRef(x_2, x_72);
lean_dec(x_2);
x_74 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2;
lean_ctor_set_tag(x_68, 2);
lean_ctor_set(x_68, 1, x_74);
lean_ctor_set(x_68, 0, x_73);
x_75 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
x_76 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3;
lean_inc(x_67);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_SourceInfo_fromRef(x_61, x_72);
lean_dec(x_61);
x_79 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4;
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5;
lean_inc(x_67);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7;
lean_inc(x_67);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_67);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12;
lean_inc(x_67);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_67);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22;
lean_inc(x_67);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1;
lean_inc(x_67);
x_90 = l_Lean_Syntax_node3(x_67, x_89, x_86, x_63, x_88);
if (lean_obj_tag(x_5) == 0)
{
x_91 = x_76;
goto block_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_5, 0);
lean_inc(x_119);
lean_dec(x_5);
x_120 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9;
lean_inc(x_67);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_67);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Array_mkArray2___rarg(x_121, x_119);
x_91 = x_122;
goto block_118;
}
block_118:
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Array_append___rarg(x_76, x_91);
lean_dec(x_91);
lean_inc(x_67);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_67);
lean_ctor_set(x_93, 1, x_75);
lean_ctor_set(x_93, 2, x_92);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8;
lean_inc(x_67);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_67);
lean_ctor_set(x_95, 1, x_75);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6;
lean_inc(x_67);
x_97 = l_Lean_Syntax_node3(x_67, x_96, x_82, x_95, x_60);
lean_inc(x_67);
x_98 = l_Lean_Syntax_node3(x_67, x_75, x_97, x_84, x_90);
x_99 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2;
lean_inc(x_67);
x_100 = l_Lean_Syntax_node1(x_67, x_99, x_98);
x_101 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2;
lean_inc(x_67);
x_102 = l_Lean_Syntax_node1(x_67, x_101, x_100);
x_103 = l_Lean_Syntax_node5(x_67, x_3, x_68, x_93, x_77, x_80, x_102);
x_104 = l_Lean_Elab_Tactic_evalTactic(x_103, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_64, 0);
lean_inc(x_105);
lean_dec(x_64);
x_106 = lean_array_push(x_76, x_105);
x_107 = l_Array_append___rarg(x_76, x_106);
lean_dec(x_106);
lean_inc(x_67);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_67);
lean_ctor_set(x_108, 1, x_75);
lean_ctor_set(x_108, 2, x_107);
x_109 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6;
lean_inc(x_67);
x_110 = l_Lean_Syntax_node3(x_67, x_109, x_82, x_108, x_60);
lean_inc(x_67);
x_111 = l_Lean_Syntax_node3(x_67, x_75, x_110, x_84, x_90);
x_112 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2;
lean_inc(x_67);
x_113 = l_Lean_Syntax_node1(x_67, x_112, x_111);
x_114 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2;
lean_inc(x_67);
x_115 = l_Lean_Syntax_node1(x_67, x_114, x_113);
x_116 = l_Lean_Syntax_node5(x_67, x_3, x_68, x_93, x_77, x_80, x_115);
x_117 = l_Lean_Elab_Tactic_evalTactic(x_116, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
return x_117;
}
}
}
else
{
lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_123 = lean_ctor_get(x_68, 1);
lean_inc(x_123);
lean_dec(x_68);
x_124 = 1;
x_125 = l_Lean_SourceInfo_fromRef(x_2, x_124);
lean_dec(x_2);
x_126 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2;
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9;
x_129 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3;
lean_inc(x_67);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_67);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_129);
x_131 = l_Lean_SourceInfo_fromRef(x_61, x_124);
lean_dec(x_61);
x_132 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4;
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5;
lean_inc(x_67);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_67);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7;
lean_inc(x_67);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_67);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12;
lean_inc(x_67);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_67);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22;
lean_inc(x_67);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_67);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1;
lean_inc(x_67);
x_143 = l_Lean_Syntax_node3(x_67, x_142, x_139, x_63, x_141);
if (lean_obj_tag(x_5) == 0)
{
x_144 = x_129;
goto block_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_5, 0);
lean_inc(x_172);
lean_dec(x_5);
x_173 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9;
lean_inc(x_67);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_67);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Array_mkArray2___rarg(x_174, x_172);
x_144 = x_175;
goto block_171;
}
block_171:
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Array_append___rarg(x_129, x_144);
lean_dec(x_144);
lean_inc(x_67);
x_146 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_146, 0, x_67);
lean_ctor_set(x_146, 1, x_128);
lean_ctor_set(x_146, 2, x_145);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_147 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8;
lean_inc(x_67);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_67);
lean_ctor_set(x_148, 1, x_128);
lean_ctor_set(x_148, 2, x_147);
x_149 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6;
lean_inc(x_67);
x_150 = l_Lean_Syntax_node3(x_67, x_149, x_135, x_148, x_60);
lean_inc(x_67);
x_151 = l_Lean_Syntax_node3(x_67, x_128, x_150, x_137, x_143);
x_152 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2;
lean_inc(x_67);
x_153 = l_Lean_Syntax_node1(x_67, x_152, x_151);
x_154 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2;
lean_inc(x_67);
x_155 = l_Lean_Syntax_node1(x_67, x_154, x_153);
x_156 = l_Lean_Syntax_node5(x_67, x_3, x_127, x_146, x_130, x_133, x_155);
x_157 = l_Lean_Elab_Tactic_evalTactic(x_156, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_123);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_158 = lean_ctor_get(x_64, 0);
lean_inc(x_158);
lean_dec(x_64);
x_159 = lean_array_push(x_129, x_158);
x_160 = l_Array_append___rarg(x_129, x_159);
lean_dec(x_159);
lean_inc(x_67);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_67);
lean_ctor_set(x_161, 1, x_128);
lean_ctor_set(x_161, 2, x_160);
x_162 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6;
lean_inc(x_67);
x_163 = l_Lean_Syntax_node3(x_67, x_162, x_135, x_161, x_60);
lean_inc(x_67);
x_164 = l_Lean_Syntax_node3(x_67, x_128, x_163, x_137, x_143);
x_165 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2;
lean_inc(x_67);
x_166 = l_Lean_Syntax_node1(x_67, x_165, x_164);
x_167 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2;
lean_inc(x_67);
x_168 = l_Lean_Syntax_node1(x_67, x_167, x_166);
x_169 = l_Lean_Syntax_node5(x_67, x_3, x_127, x_146, x_130, x_133, x_168);
x_170 = l_Lean_Elab_Tactic_evalTactic(x_169, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_123);
return x_170;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Conv_evalConv___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(2u);
lean_inc(x_17);
x_20 = l_Lean_Syntax_matchesNull(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Syntax_getArg(x_17, x_16);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1(x_1, x_15, x_11, x_24, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1(x_1, x_15, x_11, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Conv_evalConv___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalConv", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConv), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l_Lean_Elab_Tactic_Conv_evalConv___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(174u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(185u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(174u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(174u);
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(59u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalFirst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalFirst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("first", 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalFirst", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFirst___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(187u);
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(188u);
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(56u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(18u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(187u);
x_2 = lean_unsigned_to_nat(60u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(187u);
x_2 = lean_unsigned_to_nat(69u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(60u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(69u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Reduce(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1 = _init_l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1);
l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__2 = _init_l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__2);
l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Tactic_Conv_convert___spec__1___closed__1);
l_Lean_Elab_Tactic_Conv_convert___closed__1 = _init_l_Lean_Elab_Tactic_Conv_convert___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_convert___closed__1);
l_Lean_Elab_Tactic_Conv_convert___closed__2 = _init_l_Lean_Elab_Tactic_Conv_convert___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_convert___closed__2);
l_Lean_Elab_Tactic_Conv_convert___closed__3 = _init_l_Lean_Elab_Tactic_Conv_convert___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_convert___closed__3);
l_Lean_Elab_Tactic_Conv_convert___closed__4 = _init_l_Lean_Elab_Tactic_Conv_convert___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_convert___closed__4);
l_Lean_Elab_Tactic_Conv_convert___closed__5 = _init_l_Lean_Elab_Tactic_Conv_convert___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_convert___closed__5);
l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__1);
l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lambda__1___closed__2);
l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalWhnf___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__9);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__10);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__11 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__11();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__11);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalReduce___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalReduce___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalReduce___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalZeta___rarg___lambda__1___closed__2);
l_Lean_Elab_Tactic_Conv_evalZeta___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalZeta___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalZeta___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__1);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__2);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__3);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__4);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__5);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__6);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__7);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__8 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__8);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__9);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__10);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__11);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__12);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__13 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__13);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__14);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__15);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__16 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__16);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__17);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__18);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__19 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__19);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__20);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__21);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lambda__2___closed__22);
l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__2);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__3);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__4);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__5);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__6);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__7);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__8);
l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9 = _init_l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___lambda__1___closed__9);
l_Lean_Elab_Tactic_Conv_evalConv___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalConv___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
