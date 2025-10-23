// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Action
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
static lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__4;
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_Action_done___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_Action_ungroup_spec__0(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object*);
static lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instToMessageDataActionResult;
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse;
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
static lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2;
static lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1;
static lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofSyntax(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofSyntax(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("closed ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stuck ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1;
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__0(x_2, x_4);
x_6 = l_Lean_MessageData_ofList(x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3;
x_10 = lean_box(0);
x_11 = l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__1(x_8, x_10);
x_12 = l_List_mapTR_loop___at___Lean_Meta_Grind_ActionResult_toMessageData_spec__2(x_11, x_10);
x_13 = l_Lean_MessageData_ofList(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_ActionResult_toMessageData), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instToMessageDataActionResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_skip___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_skip(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_done___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*17);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_apply_9(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_done___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_done___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_done(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_2);
x_12 = lean_apply_11(x_1, x_3, x_2, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_andThen___lam__0___boxed), 11, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_5);
x_15 = lean_apply_11(x_1, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_andThen___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_andThen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_apply_1(x_2, x_14);
x_16 = l_Lean_Meta_Grind_Action_andThen(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_instAndThen() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed), 13, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_instAndThen___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_apply_11(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_5);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_orElse___lam__0___boxed), 12, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_5);
x_15 = lean_apply_11(x_1, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Action_orElse___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_orElse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_apply_1(x_2, x_14);
x_16 = l_Lean_Meta_Grind_Action_orElse(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_instOrElse() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed), 13, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_instOrElse___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Action_loop___redArg(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 1)
{
lean_object* x_15; 
lean_dec_ref(x_2);
x_15 = lean_apply_9(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_4);
x_19 = lean_apply_11(x_2, x_3, x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_loop___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Action_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Action_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*17);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_run___lam__0___boxed), 9, 0);
lean_inc_ref(x_11);
x_12 = lean_apply_11(x_2, x_1, x_11, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Action_run___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_3);
x_12 = lean_apply_11(x_1, x_2, x_3, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_4);
x_13 = lean_apply_11(x_1, x_2, x_4, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_skipIfNA___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Action_skipIfNA(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindStep", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__4;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__6;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__8;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
x_3 = lean_box(2);
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__9;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__10;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_4);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__9;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_8);
x_11 = l_Lean_Syntax_matchesNull(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__9;
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__9;
return x_15;
}
else
{
return x_6;
}
}
}
else
{
lean_dec(x_8);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Grind_Action_mkGrindStep(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Grind_Action_mkGrindStep(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__8;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindSeq", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindSeq1Indented", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at___Lean_Meta_Grind_Action_mkGrindSeq_spec__0(x_1, x_2);
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__8;
x_5 = lean_box(2);
x_6 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1;
x_7 = l_List_intersperseTR___redArg(x_6, x_3);
x_8 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
x_9 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
x_10 = lean_array_mk(x_7);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__6;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_array_push(x_12, x_14);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_dec_ref(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_Syntax_structEq(x_6, x_8);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("next", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=>", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("done", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(0);
lean_inc(x_1);
x_22 = l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 5);
x_4 = x_1;
x_5 = x_23;
x_6 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 5);
x_25 = 0;
x_26 = l_Lean_SourceInfo_fromRef(x_24, x_25);
x_27 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4;
x_28 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__5;
lean_inc(x_26);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Syntax_node1(x_26, x_28, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
x_4 = x_31;
x_5 = x_24;
x_6 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = l_Lean_Meta_Grind_Action_mkGrindSeq(x_4);
x_8 = 0;
x_9 = l_Lean_SourceInfo_fromRef(x_5, x_8);
x_10 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0;
x_11 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
lean_inc(x_9);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__8;
x_14 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2;
lean_inc(x_9);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3;
lean_inc(x_9);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Syntax_node4(x_9, x_11, x_12, x_15, x_17, x_7);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Action_mkGrindNext(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skip", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4;
x_2 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__3;
x_3 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__2;
x_4 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
x_5 = l_Lean_Meta_Grind_Action_mkGrindStep___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_List_beq___at___Lean_Meta_Grind_Action_mkGrindNext_spec__0(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_2, 5);
x_4 = x_1;
x_5 = x_20;
x_6 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 5);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4;
x_25 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5;
lean_inc(x_23);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Syntax_node1(x_23, x_25, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
x_4 = x_28;
x_5 = x_21;
x_6 = lean_box(0);
goto block_17;
}
block_17:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Meta_Grind_Action_mkGrindSeq(x_4);
x_8 = 0;
x_9 = l_Lean_SourceInfo_fromRef(x_5, x_8);
x_10 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1;
x_11 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2;
lean_inc(x_9);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3;
lean_inc(x_9);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Syntax_node3(x_9, x_10, x_12, x_7, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_8);
lean_inc_ref(x_4);
x_11 = lean_apply_9(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*8);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_8);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_17; 
lean_free_object(x_13);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_18, x_8);
lean_dec_ref(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_12, 0, x_23);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_28, x_8);
lean_dec_ref(x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_dec_ref(x_8);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*8);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_8);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_12);
return x_38;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_40 = x_12;
} else {
 lean_dec_ref(x_12);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_39, x_8);
lean_dec_ref(x_8);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec_ref(x_8);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_12);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
lean_dec_ref(x_8);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_13, 0);
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_group___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_group___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_group(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_Action_ungroup_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_4);
x_11 = lean_apply_9(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*8);
lean_dec(x_15);
if (x_16 == 0)
{
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
lean_inc(x_19);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_19, x_23);
x_25 = l_Lean_Syntax_matchesNull(x_24, x_22);
if (x_25 == 0)
{
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Syntax_getArg(x_19, x_26);
x_28 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
lean_inc(x_27);
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_27);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Syntax_getArg(x_27, x_22);
lean_dec(x_27);
x_31 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_30);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
uint8_t x_33; 
lean_inc(x_18);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_12, 0);
lean_dec(x_34);
x_35 = l_Lean_Syntax_getArg(x_30, x_22);
lean_dec(x_30);
x_36 = l_Lean_Syntax_getArgs(x_35);
lean_dec(x_35);
x_37 = l_Lean_Syntax_TSepArray_getElems___redArg(x_36);
lean_dec_ref(x_36);
x_38 = lean_array_to_list(x_37);
x_39 = l_List_mapTR_loop___at___Lean_Meta_Grind_Action_ungroup_spec__0(x_38, x_18);
lean_ctor_set(x_12, 0, x_39);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
x_40 = l_Lean_Syntax_getArg(x_30, x_22);
lean_dec(x_30);
x_41 = l_Lean_Syntax_getArgs(x_40);
lean_dec(x_40);
x_42 = l_Lean_Syntax_TSepArray_getElems___redArg(x_41);
lean_dec_ref(x_41);
x_43 = lean_array_to_list(x_42);
x_44 = l_List_mapTR_loop___at___Lean_Meta_Grind_Action_ungroup_spec__0(x_43, x_18);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_13, 0, x_45);
return x_13;
}
}
}
}
}
}
else
{
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*8);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_12);
return x_48;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_12);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 1);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
lean_inc(x_52);
x_54 = l_Lean_Syntax_isOfKind(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_12);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_unsigned_to_nat(1u);
x_58 = l_Lean_Syntax_getArg(x_52, x_57);
x_59 = l_Lean_Syntax_matchesNull(x_58, x_56);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_12);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_unsigned_to_nat(3u);
x_62 = l_Lean_Syntax_getArg(x_52, x_61);
x_63 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
lean_inc(x_62);
x_64 = l_Lean_Syntax_isOfKind(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_12);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Syntax_getArg(x_62, x_56);
lean_dec(x_62);
x_67 = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
lean_inc(x_66);
x_68 = l_Lean_Syntax_isOfKind(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_12);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_51);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_70 = x_12;
} else {
 lean_dec_ref(x_12);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Syntax_getArg(x_66, x_56);
lean_dec(x_66);
x_72 = l_Lean_Syntax_getArgs(x_71);
lean_dec(x_71);
x_73 = l_Lean_Syntax_TSepArray_getElems___redArg(x_72);
lean_dec_ref(x_72);
x_74 = lean_array_to_list(x_73);
x_75 = l_List_mapTR_loop___at___Lean_Meta_Grind_Action_ungroup_spec__0(x_74, x_51);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_12);
return x_78;
}
}
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_12);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_12);
x_80 = !lean_is_exclusive(x_13);
if (x_80 == 0)
{
return x_13;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_13, 0);
lean_inc(x_81);
lean_dec(x_13);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_dec_ref(x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_ungroup___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_ungroup___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_ungroup(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_15; 
lean_free_object(x_11);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_1, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_1);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_1);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
return x_36;
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
lean_dec_ref(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*8);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_1);
return x_39;
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_41 = x_1;
} else {
 lean_dec_ref(x_1);
 x_41 = lean_box(0);
}
x_42 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_40);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
lean_dec(x_40);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_1);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_concatTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; 
lean_free_object(x_10);
x_15 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*8);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Action_closeWith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_mk_ref(x_1);
lean_inc(x_11);
x_12 = lean_apply_9(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed), 10, 2);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_apply_9(x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec_ref(x_4);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*17);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_2);
x_24 = lean_apply_9(x_5, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec_ref(x_5);
x_25 = l_Lean_Meta_Grind_Action_closeWith(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_terminalAction___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_terminalAction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_mk_ref(x_1);
lean_inc(x_11);
x_12 = lean_apply_9(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_st_mk_ref(x_1);
lean_inc(x_10);
x_11 = lean_grind_process_new_facts(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_st_ref_get(x_10);
x_15 = lean_st_ref_get(x_10);
lean_dec(x_10);
lean_dec_ref(x_15);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_16 = lean_st_ref_get(x_10);
x_17 = lean_st_ref_get(x_10);
lean_dec(x_10);
lean_dec_ref(x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed), 10, 2);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_unbox(x_18);
switch (x_19) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_apply_9(x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_apply_9(x_5, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_4);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed), 9, 1);
lean_closure_set(x_26, 0, x_24);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_27 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*17);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_30 = lean_apply_9(x_5, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Meta_Grind_Action_concatTactic(x_31, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_32;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_30;
}
}
else
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec_ref(x_5);
x_33 = l_Lean_Meta_Grind_Action_closeWith(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
default: 
{
lean_object* x_37; 
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_37 = l_Lean_Meta_Grind_Action_closeWith(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_solverAction___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Action_solverAction___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Action_solverAction(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_getConfig___redArg(x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = l_Lean_Meta_Grind_saveState___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*8);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Grind_saveState___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_31 = x_25;
} else {
 lean_dec_ref(x_25);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
return x_6;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(x_2, x_3, x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Action_saveStateIfTracing(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_saveState___redArg(x_4, x_6, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_Grind_SavedState_restore___redArg(x_11, x_4, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = l_Lean_Meta_Grind_SavedState_restore___redArg(x_11, x_4, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_21);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_SavedState_restore___redArg(x_1, x_6, x_8, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec_ref(x_12);
x_13 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(x_2, x_9);
x_14 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 2);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
lean_ctor_set_uint8(x_14, sizeof(void*)*8, x_20);
x_21 = l_Lean_Meta_Grind_evalTactic(x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_List_isEmpty___redArg(x_23);
lean_dec(x_23);
x_25 = lean_box(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_List_isEmpty___redArg(x_26);
lean_dec(x_26);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_36; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
x_36 = l_Lean_Exception_isInterrupt(x_31);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_31);
lean_dec(x_31);
x_32 = x_37;
goto block_35;
}
else
{
lean_dec(x_31);
x_32 = x_36;
goto block_35;
}
block_35:
{
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_21);
x_33 = lean_box(x_32);
if (lean_is_scalar(x_16)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_16;
}
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_dec(x_16);
return x_21;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_44; 
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
lean_inc(x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_44 = l_Lean_Exception_isInterrupt(x_38);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isRuntime(x_38);
lean_dec(x_38);
x_40 = x_45;
goto block_43;
}
else
{
lean_dec(x_38);
x_40 = x_44;
goto block_43;
}
block_43:
{
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
x_41 = lean_box(x_40);
if (lean_is_scalar(x_16)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_16;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_dec(x_16);
return x_39;
}
}
}
}
}
else
{
uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_46 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 1);
x_47 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 2);
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
x_50 = lean_ctor_get(x_14, 2);
x_51 = lean_ctor_get(x_14, 3);
x_52 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 3);
x_53 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 4);
x_54 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 5);
x_55 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 6);
x_56 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 7);
x_57 = lean_ctor_get(x_14, 4);
x_58 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 8);
x_59 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 9);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 10);
x_61 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 11);
x_62 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 12);
x_63 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 13);
x_64 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 14);
x_65 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 15);
x_66 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 16);
x_67 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 17);
x_68 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 18);
x_69 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 19);
x_70 = lean_ctor_get(x_14, 5);
x_71 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 20);
x_72 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 21);
x_73 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 22);
x_74 = lean_ctor_get(x_14, 6);
x_75 = lean_ctor_get(x_14, 7);
x_76 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 23);
x_77 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 24);
x_78 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 25);
x_79 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 26);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_70);
lean_inc(x_57);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_80 = 0;
x_81 = lean_alloc_ctor(0, 8, 27);
lean_ctor_set(x_81, 0, x_48);
lean_ctor_set(x_81, 1, x_49);
lean_ctor_set(x_81, 2, x_50);
lean_ctor_set(x_81, 3, x_51);
lean_ctor_set(x_81, 4, x_57);
lean_ctor_set(x_81, 5, x_70);
lean_ctor_set(x_81, 6, x_74);
lean_ctor_set(x_81, 7, x_75);
lean_ctor_set_uint8(x_81, sizeof(void*)*8, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 1, x_46);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 2, x_47);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 3, x_52);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 4, x_53);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 5, x_54);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 6, x_55);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 7, x_56);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 8, x_58);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 9, x_59);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 10, x_60);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 11, x_61);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 12, x_62);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 13, x_63);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 14, x_64);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 15, x_65);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 16, x_66);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 17, x_67);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 18, x_68);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 19, x_69);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 20, x_71);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 21, x_72);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 22, x_73);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 23, x_76);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 24, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 25, x_78);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 26, x_79);
lean_ctor_set(x_5, 2, x_81);
x_82 = l_Lean_Meta_Grind_evalTactic(x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_16);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = l_List_isEmpty___redArg(x_83);
lean_dec(x_83);
x_86 = lean_box(x_85);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_95; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_89 = x_82;
} else {
 lean_dec_ref(x_82);
 x_89 = lean_box(0);
}
lean_inc(x_88);
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
x_95 = l_Lean_Exception_isInterrupt(x_88);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Lean_Exception_isRuntime(x_88);
lean_dec(x_88);
x_91 = x_96;
goto block_94;
}
else
{
lean_dec(x_88);
x_91 = x_95;
goto block_94;
}
block_94:
{
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_90);
x_92 = lean_box(x_91);
if (lean_is_scalar(x_16)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_16;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
lean_dec(x_16);
return x_90;
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_97 = lean_ctor_get(x_5, 0);
x_98 = lean_ctor_get(x_5, 1);
x_99 = lean_ctor_get_uint8(x_5, sizeof(void*)*12);
x_100 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
x_101 = lean_ctor_get(x_5, 3);
x_102 = lean_ctor_get(x_5, 4);
x_103 = lean_ctor_get(x_5, 5);
x_104 = lean_ctor_get(x_5, 6);
x_105 = lean_ctor_get(x_5, 7);
x_106 = lean_ctor_get(x_5, 8);
x_107 = lean_ctor_get(x_5, 9);
x_108 = lean_ctor_get(x_5, 10);
x_109 = lean_ctor_get(x_5, 11);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_5);
x_110 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 1);
x_111 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 2);
x_112 = lean_ctor_get(x_14, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_14, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_14, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_14, 3);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 3);
x_117 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 4);
x_118 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 5);
x_119 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 6);
x_120 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 7);
x_121 = lean_ctor_get(x_14, 4);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 8);
x_123 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 9);
x_124 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 10);
x_125 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 11);
x_126 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 12);
x_127 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 13);
x_128 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 14);
x_129 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 15);
x_130 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 16);
x_131 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 17);
x_132 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 18);
x_133 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 19);
x_134 = lean_ctor_get(x_14, 5);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 20);
x_136 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 21);
x_137 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 22);
x_138 = lean_ctor_get(x_14, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_14, 7);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 23);
x_141 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 24);
x_142 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 25);
x_143 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 26);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 lean_ctor_release(x_14, 7);
 x_144 = x_14;
} else {
 lean_dec_ref(x_14);
 x_144 = lean_box(0);
}
x_145 = 0;
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 8, 27);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_112);
lean_ctor_set(x_146, 1, x_113);
lean_ctor_set(x_146, 2, x_114);
lean_ctor_set(x_146, 3, x_115);
lean_ctor_set(x_146, 4, x_121);
lean_ctor_set(x_146, 5, x_134);
lean_ctor_set(x_146, 6, x_138);
lean_ctor_set(x_146, 7, x_139);
lean_ctor_set_uint8(x_146, sizeof(void*)*8, x_145);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 1, x_110);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 2, x_111);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 3, x_116);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 4, x_117);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 5, x_118);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 6, x_119);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 7, x_120);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 8, x_122);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 9, x_123);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 10, x_124);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 11, x_125);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 12, x_126);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 13, x_127);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 14, x_128);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 15, x_129);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 16, x_130);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 17, x_131);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 18, x_132);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 19, x_133);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 20, x_135);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 21, x_136);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 22, x_137);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 23, x_140);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 24, x_141);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 25, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*8 + 26, x_143);
x_147 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_147, 0, x_97);
lean_ctor_set(x_147, 1, x_98);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_101);
lean_ctor_set(x_147, 4, x_102);
lean_ctor_set(x_147, 5, x_103);
lean_ctor_set(x_147, 6, x_104);
lean_ctor_set(x_147, 7, x_105);
lean_ctor_set(x_147, 8, x_106);
lean_ctor_set(x_147, 9, x_107);
lean_ctor_set(x_147, 10, x_108);
lean_ctor_set(x_147, 11, x_109);
lean_ctor_set_uint8(x_147, sizeof(void*)*12, x_99);
lean_ctor_set_uint8(x_147, sizeof(void*)*12 + 1, x_100);
x_148 = l_Lean_Meta_Grind_evalTactic(x_3, x_15, x_4, x_147, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_16);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = l_List_isEmpty___redArg(x_149);
lean_dec(x_149);
x_152 = lean_box(x_151);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_161; 
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_155 = x_148;
} else {
 lean_dec_ref(x_148);
 x_155 = lean_box(0);
}
lean_inc(x_154);
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
x_161 = l_Lean_Exception_isInterrupt(x_154);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Exception_isRuntime(x_154);
lean_dec(x_154);
x_157 = x_162;
goto block_160;
}
else
{
lean_dec(x_154);
x_157 = x_161;
goto block_160;
}
block_160:
{
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_156);
x_158 = lean_box(x_157);
if (lean_is_scalar(x_16)) {
 x_159 = lean_alloc_ctor(0, 1, 0);
} else {
 x_159 = x_16;
}
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
else
{
lean_dec(x_16);
return x_156;
}
}
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_12);
if (x_163 == 0)
{
return x_12;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_12, 0);
lean_inc(x_164);
lean_dec(x_12);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed), 11, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_2);
x_17 = l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_withoutModifyingState___at___Lean_Meta_Grind_Action_checkSeqAt_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_checkSeqAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generated tactic cannot close the goal", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nInitial goal\n", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(x_4, x_5, x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_13 = lean_apply_9(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_15);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_Action_checkSeqAt(x_12, x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_free_object(x_16);
lean_inc(x_15);
lean_dec_ref(x_14);
x_20 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_15, x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1;
x_25 = l_Lean_MessageData_ofSyntax(x_22);
x_26 = l_Lean_indentD(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_23);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
x_31 = l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(x_30, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec_ref(x_1);
x_37 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1;
x_38 = l_Lean_MessageData_ofSyntax(x_35);
x_39 = l_Lean_indentD(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_36);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(x_44, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_15);
lean_dec_ref(x_14);
x_51 = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(x_15, x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec_ref(x_1);
x_55 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1;
x_56 = l_Lean_MessageData_ofSyntax(x_52);
x_57 = l_Lean_indentD(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
if (lean_is_scalar(x_53)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_53;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_54);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(x_62, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_14);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_16);
if (x_68 == 0)
{
return x_16;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_16, 0);
lean_inc(x_69);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
else
{
uint8_t x_71; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
return x_11;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_11, 0);
lean_inc(x_72);
lean_dec(x_11);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_checkTactic___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___Lean_Meta_Grind_Action_checkTactic_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Action_checkTactic___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Action_checkTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0 = _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0);
l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1 = _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1);
l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2 = _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2);
l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3 = _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3);
l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0 = _init_l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0);
l_Lean_Meta_Grind_instToMessageDataActionResult = _init_l_Lean_Meta_Grind_instToMessageDataActionResult();
lean_mark_persistent(l_Lean_Meta_Grind_instToMessageDataActionResult);
l_Lean_Meta_Grind_Action_done___redArg___closed__0 = _init_l_Lean_Meta_Grind_Action_done___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_done___redArg___closed__0);
l_Lean_Meta_Grind_Action_instAndThen = _init_l_Lean_Meta_Grind_Action_instAndThen();
lean_mark_persistent(l_Lean_Meta_Grind_Action_instAndThen);
l_Lean_Meta_Grind_Action_instOrElse = _init_l_Lean_Meta_Grind_Action_instOrElse();
lean_mark_persistent(l_Lean_Meta_Grind_Action_instOrElse);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__0 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__0);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__1 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__2 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__2);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__3 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__3);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__4 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__5 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__6 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__6);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__7 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__7);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__8 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__8);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__9 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__9);
l_Lean_Meta_Grind_Action_mkGrindStep___closed__10 = _init_l_Lean_Meta_Grind_Action_mkGrindStep___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindStep___closed__10);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5);
l_Lean_Meta_Grind_Action_mkGrindSeq___closed__6 = _init_l_Lean_Meta_Grind_Action_mkGrindSeq___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__6);
l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0 = _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0);
l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1 = _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1);
l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2 = _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2);
l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3 = _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3);
l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4 = _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4);
l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__5 = _init_l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__5);
l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3);
l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4);
l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5);
l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0 = _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0);
l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1 = _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1);
l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2 = _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2);
l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3 = _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
