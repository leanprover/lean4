// Lean compiler output
// Module: Lean.Server.Test.Cancel
// Imports: public import Lean.Elab.Command public import Lean.Elab.Tactic.Basic public meta import Lean.Elab.Command public meta import Lean.Elab.Tactic.Basic
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
lean_object* lean_io_promise_new();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
lean_object* l_IO_CancelToken_new();
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_onceRef;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Test"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Cancel"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "tacticWait_for_cancel_once"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4_value),LEAN_SCALAR_PTR_LITERAL(196, 145, 139, 180, 252, 203, 159, 176)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "wait_for_cancel_once"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0 = (const lean_object*)&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "blocked"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_cancel_once_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cancelled!"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "cancelled (should never be visible)"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value)}};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Server.Test.Cancel"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_cancel_once_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "blocked!"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_unblockedCancelTk;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "tacticWait_for_unblock"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 76, 136, 155, 84, 184, 97, 226)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "wait_for_unblock"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_unblock_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_unblock_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticWait_for_unblock_async"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 2, 167, 3, 169, 184, 169, 27)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "wait_for_unblock_async"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4_value;
static lean_once_cell_t l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 120, .m_capacity = 120, .m_length = 119, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_unblock_async_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_unblock_async_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 112, 48, 102, 88, 16, 3, 203)}};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticUnblock"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticUnblock___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 134, 8, 83, 163, 213, 163, 162)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticUnblock___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unblock"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticUnblock___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticUnblock___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticUnblock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__3_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticUnblock___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticUnblock = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticUnblock___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unblocking!"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticWait_for_cancel_once_async"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 193, 26, 122, 11, 118, 196, 212)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "wait_for_cancel_once_async"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 124, .m_capacity = 124, .m_length = 123, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_cancel_once_async_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_cancel_once_async_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 122, 104, 40, 186, 125, 92, 45)}};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "tacticWait_for_main_cancel_once_async"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 72, 241, 128, 127, 64, 204, 212)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "wait_for_main_cancel_once_async"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_main_cancel_once_async_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 175, 224, 148, 39, 133, 168, 143)}};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 129, .m_capacity = 129, .m_length = 128, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_main_cancel_once_async_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_cmdOnceRef;
static const lean_string_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "commandWait_for_cancel_once_command_"};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 229, 56, 152, 161, 65, 10, 140)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value;
static const lean_string_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "wait_for_cancel_once_command"};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5_value;
static const lean_string_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5_value),((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10 = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command__ = (const lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0 = (const lean_object*)&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_commandWait_for_cancel_once_command__1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 128, .m_capacity = 128, .m_length = 127, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_commandWait_for_cancel_once_command__1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_st_mk_ref(v___x_2_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2____boxed(lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
return v_res_6_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg(){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___boxed(lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(lean_object* v_00_u03b1_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___boxed(lean_object* v_00_u03b1_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(v_00_u03b1_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = l_Lean_interruptExceptionId;
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___boxed(lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(lean_object* v_00_u03b1_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___boxed(lean_object* v_00_u03b1_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(v_00_u03b1_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___f_86_; lean_object* v___x_10271__overap_87_; lean_object* v___x_88_; 
v___f_86_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0));
v___x_10271__overap_87_ = lean_panic_fn_borrowed(v___f_86_, v_msg_76_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
v___x_88_ = lean_apply_9(v___x_10271__overap_87_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, lean_box(0));
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___boxed(lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(lean_object* v_val_100_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = l_IO_CancelToken_isSet(v_val_100_);
if (v___x_102_ == 0)
{
uint32_t v___x_103_; lean_object* v___x_104_; 
v___x_103_ = 30;
v___x_104_ = l_IO_sleep(v___x_103_);
goto _start;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg___boxed(lean_object* v_val_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_108_);
lean_dec(v_val_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(lean_object* v_s_111_){
_start:
{
lean_object* v___x_113_; lean_object* v_putStr_114_; lean_object* v___x_115_; 
v___x_113_ = lean_get_stderr();
v_putStr_114_ = lean_ctor_get(v___x_113_, 4);
lean_inc_ref(v_putStr_114_);
lean_dec_ref(v___x_113_);
v___x_115_ = lean_apply_2(v_putStr_114_, v_s_111_, lean_box(0));
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4___boxed(lean_object* v_s_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v_s_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(lean_object* v_s_119_){
_start:
{
uint32_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = 10;
v___x_122_ = lean_string_push(v_s_119_, v___x_121_);
v___x_123_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3___boxed(lean_object* v_s_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v_s_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_env_134_; lean_object* v___x_135_; lean_object* v_mctx_136_; lean_object* v_lctx_137_; lean_object* v_options_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_133_ = lean_st_ref_get(v___y_131_);
v_env_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_133_);
v___x_135_ = lean_st_ref_get(v___y_129_);
v_mctx_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_mctx_136_);
lean_dec(v___x_135_);
v_lctx_137_ = lean_ctor_get(v___y_128_, 2);
v_options_138_ = lean_ctor_get(v___y_130_, 2);
lean_inc_ref(v_options_138_);
lean_inc_ref(v_lctx_137_);
v___x_139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_139_, 0, v_env_134_);
lean_ctor_set(v___x_139_, 1, v_mctx_136_);
lean_ctor_set(v___x_139_, 2, v_lctx_137_);
lean_ctor_set(v___x_139_, 3, v_options_138_);
v___x_140_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_msgData_127_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v_msgData_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(lean_object* v_opts_149_, lean_object* v_opt_150_){
_start:
{
lean_object* v_name_151_; lean_object* v_defValue_152_; lean_object* v_map_153_; lean_object* v___x_154_; 
v_name_151_ = lean_ctor_get(v_opt_150_, 0);
v_defValue_152_ = lean_ctor_get(v_opt_150_, 1);
v_map_153_ = lean_ctor_get(v_opts_149_, 0);
v___x_154_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_153_, v_name_151_);
if (lean_obj_tag(v___x_154_) == 0)
{
uint8_t v___x_155_; 
v___x_155_ = lean_unbox(v_defValue_152_);
return v___x_155_;
}
else
{
lean_object* v_val_156_; 
v_val_156_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_val_156_);
lean_dec_ref(v___x_154_);
if (lean_obj_tag(v_val_156_) == 1)
{
uint8_t v_v_157_; 
v_v_157_ = lean_ctor_get_uint8(v_val_156_, 0);
lean_dec_ref(v_val_156_);
return v_v_157_;
}
else
{
uint8_t v___x_158_; 
lean_dec(v_val_156_);
v___x_158_ = lean_unbox(v_defValue_152_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5___boxed(lean_object* v_opts_159_, lean_object* v_opt_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_opts_159_, v_opt_160_);
lean_dec_ref(v_opt_160_);
lean_dec_ref(v_opts_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(uint8_t v___y_171_, uint8_t v_suppressElabErrors_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 1)
{
lean_object* v_pre_174_; 
v_pre_174_ = lean_ctor_get(v_x_173_, 0);
switch(lean_obj_tag(v_pre_174_))
{
case 1:
{
lean_object* v_pre_175_; 
v_pre_175_ = lean_ctor_get(v_pre_174_, 0);
switch(lean_obj_tag(v_pre_175_))
{
case 0:
{
lean_object* v_str_176_; lean_object* v_str_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_str_176_ = lean_ctor_get(v_x_173_, 1);
v_str_177_ = lean_ctor_get(v_pre_174_, 1);
v___x_178_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_179_ = lean_string_dec_eq(v_str_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_181_ = lean_string_dec_eq(v_str_177_, v___x_180_);
if (v___x_181_ == 0)
{
return v___y_171_;
}
else
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_183_ = lean_string_dec_eq(v_str_176_, v___x_182_);
if (v___x_183_ == 0)
{
return v___y_171_;
}
else
{
return v_suppressElabErrors_172_;
}
}
}
else
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_185_ = lean_string_dec_eq(v_str_176_, v___x_184_);
if (v___x_185_ == 0)
{
return v___y_171_;
}
else
{
return v_suppressElabErrors_172_;
}
}
}
case 1:
{
lean_object* v_pre_186_; 
v_pre_186_ = lean_ctor_get(v_pre_175_, 0);
if (lean_obj_tag(v_pre_186_) == 0)
{
lean_object* v_str_187_; lean_object* v_str_188_; lean_object* v_str_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_str_187_ = lean_ctor_get(v_x_173_, 1);
v_str_188_ = lean_ctor_get(v_pre_174_, 1);
v_str_189_ = lean_ctor_get(v_pre_175_, 1);
v___x_190_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_191_ = lean_string_dec_eq(v_str_189_, v___x_190_);
if (v___x_191_ == 0)
{
return v___y_171_;
}
else
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_193_ = lean_string_dec_eq(v_str_188_, v___x_192_);
if (v___x_193_ == 0)
{
return v___y_171_;
}
else
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_195_ = lean_string_dec_eq(v_str_187_, v___x_194_);
if (v___x_195_ == 0)
{
return v___y_171_;
}
else
{
return v_suppressElabErrors_172_;
}
}
}
}
else
{
return v___y_171_;
}
}
default: 
{
return v___y_171_;
}
}
}
case 0:
{
lean_object* v_str_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_str_196_ = lean_ctor_get(v_x_173_, 1);
v___x_197_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_198_ = lean_string_dec_eq(v_str_196_, v___x_197_);
if (v___x_198_ == 0)
{
return v___y_171_;
}
else
{
return v_suppressElabErrors_172_;
}
}
default: 
{
return v___y_171_;
}
}
}
else
{
return v___y_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_199_, lean_object* v_suppressElabErrors_200_, lean_object* v_x_201_){
_start:
{
uint8_t v___y_14422__boxed_202_; uint8_t v_suppressElabErrors_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v___y_14422__boxed_202_ = lean_unbox(v___y_199_);
v_suppressElabErrors_boxed_203_ = lean_unbox(v_suppressElabErrors_200_);
v_res_204_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(v___y_14422__boxed_202_, v_suppressElabErrors_boxed_203_, v_x_201_);
lean_dec(v_x_201_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(lean_object* v_ref_207_, lean_object* v_msgData_208_, uint8_t v_severity_209_, uint8_t v_isSilent_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___y_217_; uint8_t v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_253_; uint8_t v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; uint8_t v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_278_; uint8_t v___y_279_; uint8_t v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; lean_object* v___y_285_; lean_object* v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; uint8_t v___y_295_; uint8_t v___x_300_; lean_object* v___y_302_; uint8_t v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; uint8_t v___y_310_; uint8_t v___x_325_; 
v___x_300_ = 2;
v___x_325_ = l_Lean_instBEqMessageSeverity_beq(v_severity_209_, v___x_300_);
if (v___x_325_ == 0)
{
v___y_310_ = v___x_325_;
goto v___jp_309_;
}
else
{
uint8_t v___x_326_; 
lean_inc_ref(v_msgData_208_);
v___x_326_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_208_);
v___y_310_ = v___x_326_;
goto v___jp_309_;
}
v___jp_216_:
{
lean_object* v___x_226_; lean_object* v_currNamespace_227_; lean_object* v_openDecls_228_; lean_object* v_env_229_; lean_object* v_nextMacroScope_230_; lean_object* v_ngen_231_; lean_object* v_auxDeclNGen_232_; lean_object* v_traceState_233_; lean_object* v_cache_234_; lean_object* v_messages_235_; lean_object* v_infoState_236_; lean_object* v_snapshotTasks_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_251_; 
v___x_226_ = lean_st_ref_take(v___y_225_);
v_currNamespace_227_ = lean_ctor_get(v___y_224_, 6);
v_openDecls_228_ = lean_ctor_get(v___y_224_, 7);
v_env_229_ = lean_ctor_get(v___x_226_, 0);
v_nextMacroScope_230_ = lean_ctor_get(v___x_226_, 1);
v_ngen_231_ = lean_ctor_get(v___x_226_, 2);
v_auxDeclNGen_232_ = lean_ctor_get(v___x_226_, 3);
v_traceState_233_ = lean_ctor_get(v___x_226_, 4);
v_cache_234_ = lean_ctor_get(v___x_226_, 5);
v_messages_235_ = lean_ctor_get(v___x_226_, 6);
v_infoState_236_ = lean_ctor_get(v___x_226_, 7);
v_snapshotTasks_237_ = lean_ctor_get(v___x_226_, 8);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_251_ == 0)
{
v___x_239_ = v___x_226_;
v_isShared_240_ = v_isSharedCheck_251_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snapshotTasks_237_);
lean_inc(v_infoState_236_);
lean_inc(v_messages_235_);
lean_inc(v_cache_234_);
lean_inc(v_traceState_233_);
lean_inc(v_auxDeclNGen_232_);
lean_inc(v_ngen_231_);
lean_inc(v_nextMacroScope_230_);
lean_inc(v_env_229_);
lean_dec(v___x_226_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_251_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_inc(v_openDecls_228_);
lean_inc(v_currNamespace_227_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_currNamespace_227_);
lean_ctor_set(v___x_241_, 1, v_openDecls_228_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___y_223_);
lean_inc_ref(v___y_220_);
lean_inc_ref(v___y_219_);
v___x_243_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_243_, 0, v___y_219_);
lean_ctor_set(v___x_243_, 1, v___y_217_);
lean_ctor_set(v___x_243_, 2, v___y_221_);
lean_ctor_set(v___x_243_, 3, v___y_220_);
lean_ctor_set(v___x_243_, 4, v___x_242_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*5, v___y_222_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*5 + 1, v___y_218_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*5 + 2, v_isSilent_210_);
v___x_244_ = l_Lean_MessageLog_add(v___x_243_, v_messages_235_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 6, v___x_244_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_env_229_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_nextMacroScope_230_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_ngen_231_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_auxDeclNGen_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_traceState_233_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_cache_234_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_infoState_236_);
lean_ctor_set(v_reuseFailAlloc_250_, 8, v_snapshotTasks_237_);
v___x_246_ = v_reuseFailAlloc_250_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_st_ref_set(v___y_225_, v___x_246_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
v___jp_252_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_276_; 
v___x_261_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_208_);
v___x_262_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_261_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_276_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_276_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc_ref_n(v___y_259_, 2);
v___x_267_ = l_Lean_FileMap_toPosition(v___y_259_, v___y_255_);
lean_dec(v___y_255_);
v___x_268_ = l_Lean_FileMap_toPosition(v___y_259_, v___y_260_);
lean_dec(v___y_260_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_254_ == 0)
{
lean_del_object(v___x_265_);
lean_dec_ref(v___y_253_);
v___y_217_ = v___x_267_;
v___y_218_ = v___y_256_;
v___y_219_ = v___y_257_;
v___y_220_ = v___x_270_;
v___y_221_ = v___x_269_;
v___y_222_ = v___y_258_;
v___y_223_ = v_a_263_;
v___y_224_ = v___y_213_;
v___y_225_ = v___y_214_;
goto v___jp_216_;
}
else
{
uint8_t v___x_271_; 
lean_inc(v_a_263_);
v___x_271_ = l_Lean_MessageData_hasTag(v___y_253_, v_a_263_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v___x_267_);
lean_dec(v_a_263_);
v___x_272_ = lean_box(0);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_272_);
v___x_274_ = v___x_265_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_del_object(v___x_265_);
v___y_217_ = v___x_267_;
v___y_218_ = v___y_256_;
v___y_219_ = v___y_257_;
v___y_220_ = v___x_270_;
v___y_221_ = v___x_269_;
v___y_222_ = v___y_258_;
v___y_223_ = v_a_263_;
v___y_224_ = v___y_213_;
v___y_225_ = v___y_214_;
goto v___jp_216_;
}
}
}
}
v___jp_277_:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Syntax_getTailPos_x3f(v___y_282_, v___y_284_);
lean_dec(v___y_282_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_inc(v___y_285_);
v___y_253_ = v___y_278_;
v___y_254_ = v___y_279_;
v___y_255_ = v___y_285_;
v___y_256_ = v___y_280_;
v___y_257_ = v___y_281_;
v___y_258_ = v___y_284_;
v___y_259_ = v___y_283_;
v___y_260_ = v___y_285_;
goto v___jp_252_;
}
else
{
lean_object* v_val_287_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec_ref(v___x_286_);
v___y_253_ = v___y_278_;
v___y_254_ = v___y_279_;
v___y_255_ = v___y_285_;
v___y_256_ = v___y_280_;
v___y_257_ = v___y_281_;
v___y_258_ = v___y_284_;
v___y_259_ = v___y_283_;
v___y_260_ = v_val_287_;
goto v___jp_252_;
}
}
v___jp_288_:
{
lean_object* v_ref_296_; lean_object* v___x_297_; 
v_ref_296_ = l_Lean_replaceRef(v_ref_207_, v___y_294_);
v___x_297_ = l_Lean_Syntax_getPos_x3f(v_ref_296_, v___y_292_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___y_278_ = v___y_289_;
v___y_279_ = v___y_290_;
v___y_280_ = v___y_295_;
v___y_281_ = v___y_291_;
v___y_282_ = v_ref_296_;
v___y_283_ = v___y_293_;
v___y_284_ = v___y_292_;
v___y_285_ = v___x_298_;
goto v___jp_277_;
}
else
{
lean_object* v_val_299_; 
v_val_299_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_299_);
lean_dec_ref(v___x_297_);
v___y_278_ = v___y_289_;
v___y_279_ = v___y_290_;
v___y_280_ = v___y_295_;
v___y_281_ = v___y_291_;
v___y_282_ = v_ref_296_;
v___y_283_ = v___y_293_;
v___y_284_ = v___y_292_;
v___y_285_ = v_val_299_;
goto v___jp_277_;
}
}
v___jp_301_:
{
if (v___y_308_ == 0)
{
v___y_289_ = v___y_302_;
v___y_290_ = v___y_303_;
v___y_291_ = v___y_304_;
v___y_292_ = v___y_307_;
v___y_293_ = v___y_306_;
v___y_294_ = v___y_305_;
v___y_295_ = v_severity_209_;
goto v___jp_288_;
}
else
{
v___y_289_ = v___y_302_;
v___y_290_ = v___y_303_;
v___y_291_ = v___y_304_;
v___y_292_ = v___y_307_;
v___y_293_ = v___y_306_;
v___y_294_ = v___y_305_;
v___y_295_ = v___x_300_;
goto v___jp_288_;
}
}
v___jp_309_:
{
if (v___y_310_ == 0)
{
lean_object* v_fileName_311_; lean_object* v_fileMap_312_; lean_object* v_options_313_; lean_object* v_ref_314_; uint8_t v_suppressElabErrors_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___f_318_; uint8_t v___x_319_; uint8_t v___x_320_; 
v_fileName_311_ = lean_ctor_get(v___y_213_, 0);
v_fileMap_312_ = lean_ctor_get(v___y_213_, 1);
v_options_313_ = lean_ctor_get(v___y_213_, 2);
v_ref_314_ = lean_ctor_get(v___y_213_, 5);
v_suppressElabErrors_315_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*14 + 1);
v___x_316_ = lean_box(v___y_310_);
v___x_317_ = lean_box(v_suppressElabErrors_315_);
v___f_318_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_318_, 0, v___x_316_);
lean_closure_set(v___f_318_, 1, v___x_317_);
v___x_319_ = 1;
v___x_320_ = l_Lean_instBEqMessageSeverity_beq(v_severity_209_, v___x_319_);
if (v___x_320_ == 0)
{
v___y_302_ = v___f_318_;
v___y_303_ = v_suppressElabErrors_315_;
v___y_304_ = v_fileName_311_;
v___y_305_ = v_ref_314_;
v___y_306_ = v_fileMap_312_;
v___y_307_ = v___y_310_;
v___y_308_ = v___x_320_;
goto v___jp_301_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_warningAsError;
v___x_322_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_313_, v___x_321_);
v___y_302_ = v___f_318_;
v___y_303_ = v_suppressElabErrors_315_;
v___y_304_ = v_fileName_311_;
v___y_305_ = v_ref_314_;
v___y_306_ = v_fileMap_312_;
v___y_307_ = v___y_310_;
v___y_308_ = v___x_322_;
goto v___jp_301_;
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v_msgData_208_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_327_, lean_object* v_msgData_328_, lean_object* v_severity_329_, lean_object* v_isSilent_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v_severity_boxed_336_; uint8_t v_isSilent_boxed_337_; lean_object* v_res_338_; 
v_severity_boxed_336_ = lean_unbox(v_severity_329_);
v_isSilent_boxed_337_ = lean_unbox(v_isSilent_330_);
v_res_338_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_327_, v_msgData_328_, v_severity_boxed_336_, v_isSilent_boxed_337_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v_ref_327_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(lean_object* v_msgData_339_, uint8_t v_severity_340_, uint8_t v_isSilent_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_ref_351_; lean_object* v___x_352_; 
v_ref_351_ = lean_ctor_get(v___y_348_, 5);
v___x_352_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_351_, v_msgData_339_, v_severity_340_, v_isSilent_341_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1___boxed(lean_object* v_msgData_353_, lean_object* v_severity_354_, lean_object* v_isSilent_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v_severity_boxed_365_; uint8_t v_isSilent_boxed_366_; lean_object* v_res_367_; 
v_severity_boxed_365_ = lean_unbox(v_severity_354_);
v_isSilent_boxed_366_ = lean_unbox(v_isSilent_355_);
v_res_367_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v_msgData_353_, v_severity_boxed_365_, v_isSilent_boxed_366_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_367_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1));
v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_unsigned_to_nat(32u);
v___x_374_ = lean_mk_empty_array_with_capacity(v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
v___x_378_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8));
v___x_384_ = l_Lean_MessageData_ofFormat(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_389_ = lean_unsigned_to_nat(39u);
v___x_390_ = lean_unsigned_to_nat(52u);
v___x_391_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_392_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_393_ = l_mkPanicMessageWithDecl(v___x_392_, v___x_391_, v___x_390_, v___x_389_, v___x_388_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_395_ = lean_unsigned_to_nat(37u);
v___x_396_ = lean_unsigned_to_nat(44u);
v___x_397_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_398_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_399_ = l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(lean_object* v___x_400_, lean_object* v___x_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v___x_404_, uint8_t v___x_405_, lean_object* v_val_406_, lean_object* v_x_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_418_ = 2;
v___x_419_ = 0;
v___x_420_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_417_, v___x_418_, v___x_419_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_tacSnap_x3f_421_; 
lean_dec_ref(v___x_420_);
v_tacSnap_x3f_421_ = lean_ctor_get(v___y_410_, 6);
if (lean_obj_tag(v_tacSnap_x3f_421_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_423_; 
v_val_422_ = lean_ctor_get(v_tacSnap_x3f_421_, 0);
v___x_423_ = l_Lean_Core_getMessageLog___redArg(v___y_415_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; size_t v___x_429_; lean_object* v___x_430_; lean_object* v_new_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint64_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_cancelTk_x3f_444_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
v___x_425_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_424_);
v___x_426_ = lean_unsigned_to_nat(32u);
v___x_427_ = lean_mk_empty_array_with_capacity(v___x_426_);
v___x_428_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_429_ = ((size_t)5ULL);
lean_inc_n(v___x_400_, 2);
v___x_430_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_427_);
lean_ctor_set(v___x_430_, 2, v___x_400_);
lean_ctor_set(v___x_430_, 3, v___x_400_);
lean_ctor_set_usize(v___x_430_, 4, v___x_429_);
v_new_431_ = lean_ctor_get(v_val_422_, 1);
v___x_432_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4));
v___x_433_ = l_Lean_Name_mkStr5(v___x_401_, v___x_402_, v___x_403_, v___x_404_, v___x_432_);
v___x_434_ = l_Lean_Name_toString(v___x_433_, v___x_405_);
v___x_435_ = lean_box(0);
v___x_436_ = 0ULL;
v___x_437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_437_, 0, v___x_430_);
lean_ctor_set_uint64(v___x_437_, sizeof(void*)*1, v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_438_, 0, v___x_434_);
lean_ctor_set(v___x_438_, 1, v___x_425_);
lean_ctor_set(v___x_438_, 2, v___x_435_);
lean_ctor_set(v___x_438_, 3, v___x_437_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*4, v___x_419_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5);
v___x_441_ = lean_mk_empty_array_with_capacity(v___x_400_);
lean_dec(v___x_400_);
v___x_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_442_, 0, v___x_438_);
lean_ctor_set(v___x_442_, 1, v___x_439_);
lean_ctor_set(v___x_442_, 2, v___x_435_);
lean_ctor_set(v___x_442_, 3, v___x_440_);
lean_ctor_set(v___x_442_, 4, v___x_441_);
v___x_443_ = lean_io_promise_resolve(v___x_442_, v_new_431_);
v_cancelTk_x3f_444_ = lean_ctor_get(v___y_414_, 12);
if (lean_obj_tag(v_cancelTk_x3f_444_) == 1)
{
lean_object* v_ref_445_; lean_object* v_val_446_; lean_object* v___x_447_; 
v_ref_445_ = lean_ctor_get(v___y_414_, 5);
v_val_446_ = lean_ctor_get(v_cancelTk_x3f_444_, 0);
v___x_447_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_481_; 
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v___x_447_, 0);
lean_dec(v_unused_482_);
v___x_449_ = v___x_447_;
v_isShared_450_ = v_isSharedCheck_481_;
goto v_resetjp_448_;
}
else
{
lean_dec(v___x_447_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_481_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_452_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref(v___x_452_);
lean_del_object(v___x_449_);
v___x_453_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_454_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_453_, v___x_418_, v___x_419_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_465_; 
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_466_);
v___x_456_ = v___x_454_;
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_454_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = lean_io_promise_resolve(v___x_458_, v_val_406_);
v___x_460_ = l_IO_CancelToken_isSet(v_val_446_);
if (v___x_460_ == 0)
{
lean_object* v___x_462_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_462_ = v___x_456_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_458_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
else
{
lean_object* v___x_464_; 
lean_del_object(v___x_456_);
v___x_464_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_464_;
}
}
}
else
{
return v___x_454_;
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_480_; 
v_a_467_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_480_ == 0)
{
v___x_469_ = v___x_452_;
v_isShared_470_ = v_isSharedCheck_480_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_452_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_480_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_io_error_to_string(v_a_467_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 3);
lean_ctor_set(v___x_449_, 0, v___x_471_);
v___x_473_ = v___x_449_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_479_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = l_Lean_MessageData_ofFormat(v___x_473_);
lean_inc(v_ref_445_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_ref_445_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_475_);
v___x_477_ = v___x_469_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
else
{
return v___x_447_;
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13);
v___x_484_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_483_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
return v___x_484_;
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_402_);
lean_dec_ref(v___x_401_);
lean_dec(v___x_400_);
v_a_485_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_423_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_423_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_402_);
lean_dec_ref(v___x_401_);
lean_dec(v___x_400_);
v___x_493_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14);
v___x_494_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_493_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
return v___x_494_;
}
}
else
{
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_402_);
lean_dec_ref(v___x_401_);
lean_dec(v___x_400_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_495_ = _args[0];
lean_object* v___x_496_ = _args[1];
lean_object* v___x_497_ = _args[2];
lean_object* v___x_498_ = _args[3];
lean_object* v___x_499_ = _args[4];
lean_object* v___x_500_ = _args[5];
lean_object* v_val_501_ = _args[6];
lean_object* v_x_502_ = _args[7];
lean_object* v___y_503_ = _args[8];
lean_object* v___y_504_ = _args[9];
lean_object* v___y_505_ = _args[10];
lean_object* v___y_506_ = _args[11];
lean_object* v___y_507_ = _args[12];
lean_object* v___y_508_ = _args[13];
lean_object* v___y_509_ = _args[14];
lean_object* v___y_510_ = _args[15];
lean_object* v___y_511_ = _args[16];
_start:
{
uint8_t v___x_14802__boxed_512_; lean_object* v_res_513_; 
v___x_14802__boxed_512_ = lean_unbox(v___x_500_);
v_res_513_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(v___x_495_, v___x_496_, v___x_497_, v___x_498_, v___x_499_, v___x_14802__boxed_512_, v_val_501_, v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v_val_501_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(lean_object* v_x_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_525_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_526_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_527_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_528_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_529_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5));
v___x_530_ = l_Lean_Syntax_isOfKind(v_x_515_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_531_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___f_537_; lean_object* v___y_539_; 
v___x_532_ = lean_io_promise_new();
v___x_533_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_534_ = lean_st_ref_take(v___x_533_);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_box(v___x_530_);
lean_inc(v___x_532_);
v___f_537_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed), 17, 7);
lean_closure_set(v___f_537_, 0, v___x_535_);
lean_closure_set(v___f_537_, 1, v___x_525_);
lean_closure_set(v___f_537_, 2, v___x_526_);
lean_closure_set(v___f_537_, 3, v___x_527_);
lean_closure_set(v___f_537_, 4, v___x_528_);
lean_closure_set(v___f_537_, 5, v___x_536_);
lean_closure_set(v___f_537_, 6, v___x_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_555_; 
v___x_555_ = l_IO_Promise_result_x21___redArg(v___x_532_);
lean_dec(v___x_532_);
v___y_539_ = v___x_555_;
goto v___jp_538_;
}
else
{
lean_object* v_val_556_; 
lean_dec(v___x_532_);
v_val_556_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_556_);
v___y_539_ = v_val_556_;
goto v___jp_538_;
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___y_539_);
v___x_541_ = lean_st_ref_set(v___x_533_, v___x_540_);
if (lean_obj_tag(v___x_534_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v___f_537_);
v_val_542_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_551_ == 0)
{
v___x_544_ = v___x_534_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v___x_534_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_io_wait(v_val_542_);
lean_dec(v___x_546_);
v___x_547_ = lean_box(0);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
lean_ctor_set(v___x_544_, 0, v___x_547_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_9373__overap_553_; lean_object* v___x_554_; 
lean_dec(v___x_534_);
v___x_552_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_9373__overap_553_ = lean_dbg_trace(v___x_552_, v___f_537_);
lean_inc(v_a_523_);
lean_inc_ref(v_a_522_);
lean_inc(v_a_521_);
lean_inc_ref(v_a_520_);
lean_inc(v_a_519_);
lean_inc_ref(v_a_518_);
lean_inc(v_a_517_);
lean_inc_ref(v_a_516_);
v___x_554_ = lean_apply_9(v___x_9373__overap_553_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, lean_box(0));
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(lean_object* v_x_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(v_x_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(lean_object* v_val_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_568_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(lean_object* v_val_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(v_val_580_, v_b_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v_val_580_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(lean_object* v_ref_592_, lean_object* v_msgData_593_, uint8_t v_severity_594_, uint8_t v_isSilent_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_592_, v_msgData_593_, v_severity_594_, v_isSilent_595_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(lean_object* v_ref_606_, lean_object* v_msgData_607_, lean_object* v_severity_608_, lean_object* v_isSilent_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
uint8_t v_severity_boxed_619_; uint8_t v_isSilent_boxed_620_; lean_object* v_res_621_; 
v_severity_boxed_619_ = lean_unbox(v_severity_608_);
v_isSilent_boxed_620_ = lean_unbox(v_isSilent_609_);
v_res_621_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(v_ref_606_, v_msgData_607_, v_severity_boxed_619_, v_isSilent_boxed_620_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v_ref_606_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = l_IO_CancelToken_new();
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2____boxed(lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_();
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg(){
_start:
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = l_Lean_Server_Test_Cancel_unblockedCancelTk;
v___x_645_ = l_IO_CancelToken_isSet(v___x_644_);
if (v___x_645_ == 0)
{
uint32_t v___x_646_; lean_object* v___x_647_; 
v___x_646_ = 30;
v___x_647_ = l_IO_sleep(v___x_646_);
goto _start;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v_res_652_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_656_ = lean_unsigned_to_nat(37u);
v___x_657_ = lean_unsigned_to_nat(81u);
v___x_658_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_659_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_660_ = l_mkPanicMessageWithDecl(v___x_659_, v___x_658_, v___x_657_, v___x_656_, v___x_655_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(lean_object* v___x_661_, lean_object* v___x_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, uint8_t v___x_666_, lean_object* v_val_667_, lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_679_ = 2;
v___x_680_ = 0;
v___x_681_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_678_, v___x_679_, v___x_680_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_748_; 
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_749_);
v___x_683_ = v___x_681_;
v_isShared_684_ = v_isSharedCheck_748_;
goto v_resetjp_682_;
}
else
{
lean_dec(v___x_681_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_748_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_tacSnap_x3f_685_; 
v_tacSnap_x3f_685_ = lean_ctor_get(v___y_671_, 6);
if (lean_obj_tag(v_tacSnap_x3f_685_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
v_val_686_ = lean_ctor_get(v_tacSnap_x3f_685_, 0);
v___x_687_ = l_Lean_Core_getMessageLog___redArg(v___y_676_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; size_t v___x_693_; lean_object* v___x_694_; lean_object* v_new_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint64_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref(v___x_687_);
v___x_689_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_688_);
v___x_690_ = lean_unsigned_to_nat(32u);
v___x_691_ = lean_mk_empty_array_with_capacity(v___x_690_);
v___x_692_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_693_ = ((size_t)5ULL);
lean_inc_n(v___x_661_, 2);
v___x_694_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_691_);
lean_ctor_set(v___x_694_, 2, v___x_661_);
lean_ctor_set(v___x_694_, 3, v___x_661_);
lean_ctor_set_usize(v___x_694_, 4, v___x_693_);
v_new_695_ = lean_ctor_get(v_val_686_, 1);
v___x_696_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0));
v___x_697_ = l_Lean_Name_mkStr5(v___x_662_, v___x_663_, v___x_664_, v___x_665_, v___x_696_);
v___x_698_ = l_Lean_Name_toString(v___x_697_, v___x_666_);
v___x_699_ = lean_box(0);
v___x_700_ = 0ULL;
v___x_701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_701_, 0, v___x_694_);
lean_ctor_set_uint64(v___x_701_, sizeof(void*)*1, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_702_, 0, v___x_698_);
lean_ctor_set(v___x_702_, 1, v___x_689_);
lean_ctor_set(v___x_702_, 2, v___x_699_);
lean_ctor_set(v___x_702_, 3, v___x_701_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*4, v___x_680_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5);
v___x_705_ = lean_mk_empty_array_with_capacity(v___x_661_);
lean_dec(v___x_661_);
v___x_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_706_, 0, v___x_702_);
lean_ctor_set(v___x_706_, 1, v___x_703_);
lean_ctor_set(v___x_706_, 2, v___x_699_);
lean_ctor_set(v___x_706_, 3, v___x_704_);
lean_ctor_set(v___x_706_, 4, v___x_705_);
v___x_707_ = lean_io_promise_resolve(v___x_706_, v_new_695_);
v___x_708_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_736_; 
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_708_, 0);
lean_dec(v_unused_737_);
v___x_710_ = v___x_708_;
v_isShared_711_ = v_isSharedCheck_736_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_708_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_736_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v___x_712_; 
v___x_712_ = l_IO_CancelToken_isSet(v_val_667_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_del_object(v___x_683_);
v___x_713_ = lean_box(0);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_713_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_710_);
v___x_717_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_718_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_717_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref(v___x_718_);
lean_del_object(v___x_683_);
v___x_719_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_720_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_719_, v___x_679_, v___x_680_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_720_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_735_; 
v_a_721_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
v___x_723_ = v___x_718_;
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_718_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_ref_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_ref_725_ = lean_ctor_get(v___y_675_, 5);
v___x_726_ = lean_io_error_to_string(v_a_721_);
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 3);
lean_ctor_set(v___x_683_, 0, v___x_726_);
v___x_728_ = v___x_683_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_734_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = l_Lean_MessageData_ofFormat(v___x_728_);
lean_inc(v_ref_725_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_ref_725_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_730_);
v___x_732_ = v___x_723_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_683_);
return v___x_708_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_683_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec_ref(v___x_662_);
lean_dec(v___x_661_);
v_a_738_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_687_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_687_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_683_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec_ref(v___x_662_);
lean_dec(v___x_661_);
v___x_746_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2);
v___x_747_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_746_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_747_;
}
}
}
else
{
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec_ref(v___x_662_);
lean_dec(v___x_661_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_750_ = _args[0];
lean_object* v___x_751_ = _args[1];
lean_object* v___x_752_ = _args[2];
lean_object* v___x_753_ = _args[3];
lean_object* v___x_754_ = _args[4];
lean_object* v___x_755_ = _args[5];
lean_object* v_val_756_ = _args[6];
lean_object* v_x_757_ = _args[7];
lean_object* v___y_758_ = _args[8];
lean_object* v___y_759_ = _args[9];
lean_object* v___y_760_ = _args[10];
lean_object* v___y_761_ = _args[11];
lean_object* v___y_762_ = _args[12];
lean_object* v___y_763_ = _args[13];
lean_object* v___y_764_ = _args[14];
lean_object* v___y_765_ = _args[15];
lean_object* v___y_766_ = _args[16];
_start:
{
uint8_t v___x_6403__boxed_767_; lean_object* v_res_768_; 
v___x_6403__boxed_767_ = lean_unbox(v___x_755_);
v_res_768_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(v___x_750_, v___x_751_, v___x_752_, v___x_753_, v___x_754_, v___x_6403__boxed_767_, v_val_756_, v_x_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v_val_756_);
return v_res_768_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_770_ = lean_unsigned_to_nat(39u);
v___x_771_ = lean_unsigned_to_nat(76u);
v___x_772_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_773_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_774_ = l_mkPanicMessageWithDecl(v___x_773_, v___x_772_, v___x_771_, v___x_770_, v___x_769_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(lean_object* v_x_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_785_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_786_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_787_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_788_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_789_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1));
v___x_790_ = l_Lean_Syntax_isOfKind(v_x_775_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_791_;
}
else
{
lean_object* v_cancelTk_x3f_792_; 
v_cancelTk_x3f_792_ = lean_ctor_get(v_a_782_, 12);
if (lean_obj_tag(v_cancelTk_x3f_792_) == 1)
{
lean_object* v_val_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_5865__overap_798_; lean_object* v___x_799_; 
v_val_793_ = lean_ctor_get(v_cancelTk_x3f_792_, 0);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_box(v___x_790_);
lean_inc(v_val_793_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed), 17, 7);
lean_closure_set(v___f_796_, 0, v___x_794_);
lean_closure_set(v___f_796_, 1, v___x_785_);
lean_closure_set(v___f_796_, 2, v___x_786_);
lean_closure_set(v___f_796_, 3, v___x_787_);
lean_closure_set(v___f_796_, 4, v___x_788_);
lean_closure_set(v___f_796_, 5, v___x_795_);
lean_closure_set(v___f_796_, 6, v_val_793_);
v___x_797_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_5865__overap_798_ = lean_dbg_trace(v___x_797_, v___f_796_);
lean_inc(v_a_783_);
lean_inc_ref(v_a_782_);
lean_inc(v_a_781_);
lean_inc_ref(v_a_780_);
lean_inc(v_a_779_);
lean_inc_ref(v_a_778_);
lean_inc(v_a_777_);
lean_inc_ref(v_a_776_);
v___x_799_ = lean_apply_9(v___x_5865__overap_798_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, lean_box(0));
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0);
v___x_801_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_800_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(lean_object* v_x_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(v_x_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(v_b_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_834_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(lean_object* v_msg_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_5255__overap_861_; lean_object* v___x_862_; 
v___x_860_ = lean_obj_once(&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0, &l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0);
v___x_5255__overap_861_ = lean_panic_fn_borrowed(v___x_860_, v_msg_852_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_862_ = lean_apply_7(v___x_5255__overap_861_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___boxed(lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v_msg_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg(){
_start:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = l_Lean_Server_Test_Cancel_unblockedCancelTk;
v___x_874_ = l_IO_CancelToken_isSet(v___x_873_);
if (v___x_874_ == 0)
{
uint32_t v___x_875_; lean_object* v___x_876_; 
v___x_875_ = 30;
v___x_876_ = l_IO_sleep(v___x_875_);
goto _start;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(lean_object* v_ref_882_, lean_object* v_msgData_883_, uint8_t v_severity_884_, uint8_t v_isSilent_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; uint8_t v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_931_; lean_object* v___y_932_; uint8_t v___y_933_; uint8_t v___y_934_; lean_object* v___y_935_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_956_; lean_object* v___y_957_; uint8_t v___y_958_; uint8_t v___y_959_; lean_object* v___y_960_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; uint8_t v___y_967_; lean_object* v___y_968_; uint8_t v___y_969_; uint8_t v___y_970_; uint8_t v___x_975_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; uint8_t v___y_981_; uint8_t v___y_982_; uint8_t v___y_983_; uint8_t v___y_985_; uint8_t v___x_1000_; 
v___x_975_ = 2;
v___x_1000_ = l_Lean_instBEqMessageSeverity_beq(v_severity_884_, v___x_975_);
if (v___x_1000_ == 0)
{
v___y_985_ = v___x_1000_;
goto v___jp_984_;
}
else
{
uint8_t v___x_1001_; 
lean_inc_ref(v_msgData_883_);
v___x_1001_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_883_);
v___y_985_ = v___x_1001_;
goto v___jp_984_;
}
v___jp_891_:
{
lean_object* v___x_901_; lean_object* v_currNamespace_902_; lean_object* v_openDecls_903_; lean_object* v_env_904_; lean_object* v_nextMacroScope_905_; lean_object* v_ngen_906_; lean_object* v_auxDeclNGen_907_; lean_object* v_traceState_908_; lean_object* v_cache_909_; lean_object* v_messages_910_; lean_object* v_infoState_911_; lean_object* v_snapshotTasks_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_926_; 
v___x_901_ = lean_st_ref_take(v___y_900_);
v_currNamespace_902_ = lean_ctor_get(v___y_899_, 6);
v_openDecls_903_ = lean_ctor_get(v___y_899_, 7);
v_env_904_ = lean_ctor_get(v___x_901_, 0);
v_nextMacroScope_905_ = lean_ctor_get(v___x_901_, 1);
v_ngen_906_ = lean_ctor_get(v___x_901_, 2);
v_auxDeclNGen_907_ = lean_ctor_get(v___x_901_, 3);
v_traceState_908_ = lean_ctor_get(v___x_901_, 4);
v_cache_909_ = lean_ctor_get(v___x_901_, 5);
v_messages_910_ = lean_ctor_get(v___x_901_, 6);
v_infoState_911_ = lean_ctor_get(v___x_901_, 7);
v_snapshotTasks_912_ = lean_ctor_get(v___x_901_, 8);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_926_ == 0)
{
v___x_914_ = v___x_901_;
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snapshotTasks_912_);
lean_inc(v_infoState_911_);
lean_inc(v_messages_910_);
lean_inc(v_cache_909_);
lean_inc(v_traceState_908_);
lean_inc(v_auxDeclNGen_907_);
lean_inc(v_ngen_906_);
lean_inc(v_nextMacroScope_905_);
lean_inc(v_env_904_);
lean_dec(v___x_901_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_openDecls_903_);
lean_inc(v_currNamespace_902_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_currNamespace_902_);
lean_ctor_set(v___x_916_, 1, v_openDecls_903_);
v___x_917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___y_896_);
lean_inc_ref(v___y_894_);
lean_inc_ref(v___y_892_);
v___x_918_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_918_, 0, v___y_892_);
lean_ctor_set(v___x_918_, 1, v___y_893_);
lean_ctor_set(v___x_918_, 2, v___y_897_);
lean_ctor_set(v___x_918_, 3, v___y_894_);
lean_ctor_set(v___x_918_, 4, v___x_917_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*5, v___y_895_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*5 + 1, v___y_898_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*5 + 2, v_isSilent_885_);
v___x_919_ = l_Lean_MessageLog_add(v___x_918_, v_messages_910_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 6, v___x_919_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_env_904_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_nextMacroScope_905_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_ngen_906_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_auxDeclNGen_907_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_traceState_908_);
lean_ctor_set(v_reuseFailAlloc_925_, 5, v_cache_909_);
lean_ctor_set(v_reuseFailAlloc_925_, 6, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 7, v_infoState_911_);
lean_ctor_set(v_reuseFailAlloc_925_, 8, v_snapshotTasks_912_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_st_ref_set(v___y_900_, v___x_921_);
v___x_923_ = lean_box(0);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
v___jp_927_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_951_; 
v___x_936_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_883_);
v___x_937_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_936_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_951_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_951_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_951_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_inc_ref_n(v___y_930_, 2);
v___x_942_ = l_Lean_FileMap_toPosition(v___y_930_, v___y_932_);
lean_dec(v___y_932_);
v___x_943_ = l_Lean_FileMap_toPosition(v___y_930_, v___y_935_);
lean_dec(v___y_935_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_934_ == 0)
{
lean_del_object(v___x_940_);
lean_dec_ref(v___y_928_);
v___y_892_ = v___y_929_;
v___y_893_ = v___x_942_;
v___y_894_ = v___x_945_;
v___y_895_ = v___y_931_;
v___y_896_ = v_a_938_;
v___y_897_ = v___x_944_;
v___y_898_ = v___y_933_;
v___y_899_ = v___y_888_;
v___y_900_ = v___y_889_;
goto v___jp_891_;
}
else
{
uint8_t v___x_946_; 
lean_inc(v_a_938_);
v___x_946_ = l_Lean_MessageData_hasTag(v___y_928_, v_a_938_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec_ref(v___x_944_);
lean_dec_ref(v___x_942_);
lean_dec(v_a_938_);
v___x_947_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_947_);
v___x_949_ = v___x_940_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
lean_del_object(v___x_940_);
v___y_892_ = v___y_929_;
v___y_893_ = v___x_942_;
v___y_894_ = v___x_945_;
v___y_895_ = v___y_931_;
v___y_896_ = v_a_938_;
v___y_897_ = v___x_944_;
v___y_898_ = v___y_933_;
v___y_899_ = v___y_888_;
v___y_900_ = v___y_889_;
goto v___jp_891_;
}
}
}
}
v___jp_952_:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Syntax_getTailPos_x3f(v___y_957_, v___y_956_);
lean_dec(v___y_957_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_inc(v___y_960_);
v___y_928_ = v___y_953_;
v___y_929_ = v___y_954_;
v___y_930_ = v___y_955_;
v___y_931_ = v___y_956_;
v___y_932_ = v___y_960_;
v___y_933_ = v___y_958_;
v___y_934_ = v___y_959_;
v___y_935_ = v___y_960_;
goto v___jp_927_;
}
else
{
lean_object* v_val_962_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_962_);
lean_dec_ref(v___x_961_);
v___y_928_ = v___y_953_;
v___y_929_ = v___y_954_;
v___y_930_ = v___y_955_;
v___y_931_ = v___y_956_;
v___y_932_ = v___y_960_;
v___y_933_ = v___y_958_;
v___y_934_ = v___y_959_;
v___y_935_ = v_val_962_;
goto v___jp_927_;
}
}
v___jp_963_:
{
lean_object* v_ref_971_; lean_object* v___x_972_; 
v_ref_971_ = l_Lean_replaceRef(v_ref_882_, v___y_968_);
v___x_972_ = l_Lean_Syntax_getPos_x3f(v_ref_971_, v___y_967_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_unsigned_to_nat(0u);
v___y_953_ = v___y_964_;
v___y_954_ = v___y_965_;
v___y_955_ = v___y_966_;
v___y_956_ = v___y_967_;
v___y_957_ = v_ref_971_;
v___y_958_ = v___y_970_;
v___y_959_ = v___y_969_;
v___y_960_ = v___x_973_;
goto v___jp_952_;
}
else
{
lean_object* v_val_974_; 
v_val_974_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_val_974_);
lean_dec_ref(v___x_972_);
v___y_953_ = v___y_964_;
v___y_954_ = v___y_965_;
v___y_955_ = v___y_966_;
v___y_956_ = v___y_967_;
v___y_957_ = v_ref_971_;
v___y_958_ = v___y_970_;
v___y_959_ = v___y_969_;
v___y_960_ = v_val_974_;
goto v___jp_952_;
}
}
v___jp_976_:
{
if (v___y_983_ == 0)
{
v___y_964_ = v___y_978_;
v___y_965_ = v___y_977_;
v___y_966_ = v___y_979_;
v___y_967_ = v___y_982_;
v___y_968_ = v___y_980_;
v___y_969_ = v___y_981_;
v___y_970_ = v_severity_884_;
goto v___jp_963_;
}
else
{
v___y_964_ = v___y_978_;
v___y_965_ = v___y_977_;
v___y_966_ = v___y_979_;
v___y_967_ = v___y_982_;
v___y_968_ = v___y_980_;
v___y_969_ = v___y_981_;
v___y_970_ = v___x_975_;
goto v___jp_963_;
}
}
v___jp_984_:
{
if (v___y_985_ == 0)
{
lean_object* v_fileName_986_; lean_object* v_fileMap_987_; lean_object* v_options_988_; lean_object* v_ref_989_; uint8_t v_suppressElabErrors_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___f_993_; uint8_t v___x_994_; uint8_t v___x_995_; 
v_fileName_986_ = lean_ctor_get(v___y_888_, 0);
v_fileMap_987_ = lean_ctor_get(v___y_888_, 1);
v_options_988_ = lean_ctor_get(v___y_888_, 2);
v_ref_989_ = lean_ctor_get(v___y_888_, 5);
v_suppressElabErrors_990_ = lean_ctor_get_uint8(v___y_888_, sizeof(void*)*14 + 1);
v___x_991_ = lean_box(v___y_985_);
v___x_992_ = lean_box(v_suppressElabErrors_990_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_993_, 0, v___x_991_);
lean_closure_set(v___f_993_, 1, v___x_992_);
v___x_994_ = 1;
v___x_995_ = l_Lean_instBEqMessageSeverity_beq(v_severity_884_, v___x_994_);
if (v___x_995_ == 0)
{
v___y_977_ = v_fileName_986_;
v___y_978_ = v___f_993_;
v___y_979_ = v_fileMap_987_;
v___y_980_ = v_ref_989_;
v___y_981_ = v_suppressElabErrors_990_;
v___y_982_ = v___y_985_;
v___y_983_ = v___x_995_;
goto v___jp_976_;
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = l_Lean_warningAsError;
v___x_997_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_988_, v___x_996_);
v___y_977_ = v_fileName_986_;
v___y_978_ = v___f_993_;
v___y_979_ = v_fileMap_987_;
v___y_980_ = v_ref_989_;
v___y_981_ = v_suppressElabErrors_990_;
v___y_982_ = v___y_985_;
v___y_983_ = v___x_997_;
goto v___jp_976_;
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref(v_msgData_883_);
v___x_998_ = lean_box(0);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_1002_, lean_object* v_msgData_1003_, lean_object* v_severity_1004_, lean_object* v_isSilent_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_severity_boxed_1011_; uint8_t v_isSilent_boxed_1012_; lean_object* v_res_1013_; 
v_severity_boxed_1011_ = lean_unbox(v_severity_1004_);
v_isSilent_boxed_1012_ = lean_unbox(v_isSilent_1005_);
v_res_1013_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1002_, v_msgData_1003_, v_severity_boxed_1011_, v_isSilent_boxed_1012_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_ref_1002_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(lean_object* v_msgData_1014_, uint8_t v_severity_1015_, uint8_t v_isSilent_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_ref_1024_; lean_object* v___x_1025_; 
v_ref_1024_ = lean_ctor_get(v___y_1021_, 5);
v___x_1025_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1024_, v_msgData_1014_, v_severity_1015_, v_isSilent_1016_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(lean_object* v_msgData_1026_, lean_object* v_severity_1027_, lean_object* v_isSilent_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
uint8_t v_severity_boxed_1036_; uint8_t v_isSilent_boxed_1037_; lean_object* v_res_1038_; 
v_severity_boxed_1036_ = lean_unbox(v_severity_1027_);
v_isSilent_boxed_1037_ = lean_unbox(v_isSilent_1028_);
v_res_1038_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v_msgData_1026_, v_severity_boxed_1036_, v_isSilent_boxed_1037_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1040_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1041_ = lean_unsigned_to_nat(41u);
v___x_1042_ = lean_unsigned_to_nat(105u);
v___x_1043_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0));
v___x_1044_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1045_ = l_mkPanicMessageWithDecl(v___x_1044_, v___x_1043_, v___x_1042_, v___x_1041_, v___x_1040_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(lean_object* v_x_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_cancelTk_x3f_1054_; 
v_cancelTk_x3f_1054_ = lean_ctor_get(v___y_1051_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1054_) == 1)
{
lean_object* v_ref_1055_; lean_object* v_val_1056_; lean_object* v___x_1057_; 
v_ref_1055_ = lean_ctor_get(v___y_1051_, 5);
v_val_1056_ = lean_ctor_get(v_cancelTk_x3f_1054_, 0);
v___x_1057_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1084_; 
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_1057_, 0);
lean_dec(v_unused_1085_);
v___x_1059_ = v___x_1057_;
v_isShared_1060_ = v_isSharedCheck_1084_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v___x_1057_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1084_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_IO_CancelToken_isSet(v_val_1056_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_box(0);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1062_);
v___x_1064_ = v___x_1059_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_del_object(v___x_1059_);
v___x_1066_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1067_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v___x_1068_; uint8_t v___x_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; 
lean_dec_ref(v___x_1067_);
v___x_1068_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1069_ = 2;
v___x_1070_ = 0;
v___x_1071_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1068_, v___x_1069_, v___x_1070_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1071_;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1083_; 
v_a_1072_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1074_ = v___x_1067_;
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1067_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1083_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1076_ = lean_io_error_to_string(v_a_1072_);
v___x_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = l_Lean_MessageData_ofFormat(v___x_1077_);
lean_inc(v_ref_1055_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_ref_1055_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1079_);
v___x_1081_ = v___x_1074_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
else
{
return v___x_1057_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1);
v___x_1087_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1086_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed(lean_object* v_x_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(v_x_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(lean_object* v_x_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1));
v___x_1118_ = l_Lean_Syntax_isOfKind(v_x_1107_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1120_ = l_IO_CancelToken_new();
v___f_1121_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0));
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
v___x_1123_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2));
v___x_1124_ = l_Lean_Name_toString(v___x_1123_, v___x_1118_);
lean_inc_ref(v___x_1122_);
v___x_1125_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1121_, v___x_1122_, v___x_1124_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_apply_1(v_a_1126_, v___x_1127_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_io_as_task(v___x_1128_, v___x_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
lean_ctor_set(v___x_1133_, 2, v___x_1122_);
lean_ctor_set(v___x_1133_, 3, v___x_1130_);
v___x_1134_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1133_, v_a_1115_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v___x_1134_);
v___x_1135_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1136_ = 2;
v___x_1137_ = 0;
v___x_1138_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1135_, v___x_1136_, v___x_1137_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1138_;
}
else
{
return v___x_1134_;
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___x_1122_);
v_a_1139_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1125_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1125_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___boxed(lean_object* v_x_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(v_x_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(v_b_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(lean_object* v_ref_1176_, lean_object* v_msgData_1177_, uint8_t v_severity_1178_, uint8_t v_isSilent_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1176_, v_msgData_1177_, v_severity_1178_, v_isSilent_1179_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___boxed(lean_object* v_ref_1188_, lean_object* v_msgData_1189_, lean_object* v_severity_1190_, lean_object* v_isSilent_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v_severity_boxed_1199_; uint8_t v_isSilent_boxed_1200_; lean_object* v_res_1201_; 
v_severity_boxed_1199_ = lean_unbox(v_severity_1190_);
v_isSilent_boxed_1200_ = lean_unbox(v_isSilent_1191_);
v_res_1201_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(v_ref_1188_, v_msgData_1189_, v_severity_boxed_1199_, v_isSilent_boxed_1200_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v_ref_1188_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(lean_object* v_x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = l_Lean_Server_Test_Cancel_unblockedCancelTk;
v___x_1229_ = l_IO_CancelToken_set(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed(lean_object* v_x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(v_x_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(lean_object* v_x_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1));
v___x_1255_ = l_Lean_Syntax_isOfKind(v_x_1244_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1256_;
}
else
{
lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_426__overap_1259_; lean_object* v___x_1260_; 
v___f_1257_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0));
v___x_1258_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1));
v___x_426__overap_1259_ = lean_dbg_trace(v___x_1258_, v___f_1257_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
v___x_1260_ = lean_apply_9(v___x_426__overap_1259_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, lean_box(0));
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___boxed(lean_object* v_x_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(v_x_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(lean_object* v_x_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1299_ = 2;
v___x_1300_ = 0;
v___x_1301_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1298_, v___x_1299_, v___x_1300_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed(lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(lean_object* v_val_1313_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_IO_CancelToken_isSet(v_val_1313_);
if (v___x_1315_ == 0)
{
uint32_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = 30;
v___x_1317_ = l_IO_sleep(v___x_1316_);
goto _start;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(lean_object* v_val_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1321_);
lean_dec(v_val_1321_);
return v_res_1323_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1325_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1326_ = lean_unsigned_to_nat(41u);
v___x_1327_ = lean_unsigned_to_nat(139u);
v___x_1328_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0));
v___x_1329_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1330_ = l_mkPanicMessageWithDecl(v___x_1329_, v___x_1328_, v___x_1327_, v___x_1326_, v___x_1325_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(lean_object* v_val_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_cancelTk_x3f_1340_; 
v_cancelTk_x3f_1340_ = lean_ctor_get(v___y_1337_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1340_) == 1)
{
lean_object* v_ref_1341_; lean_object* v_val_1342_; lean_object* v___x_1343_; 
v_ref_1341_ = lean_ctor_get(v___y_1337_, 5);
v_val_1342_ = lean_ctor_get(v_cancelTk_x3f_1340_, 0);
v___x_1343_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1379_; 
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1343_, 0);
lean_dec(v_unused_1380_);
v___x_1345_ = v___x_1343_;
v_isShared_1346_ = v_isSharedCheck_1379_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v___x_1343_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1379_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1348_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; uint8_t v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; 
lean_dec_ref(v___x_1348_);
lean_del_object(v___x_1345_);
v___x_1349_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1350_ = 2;
v___x_1351_ = 0;
v___x_1352_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1349_, v___x_1350_, v___x_1351_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1363_; 
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1364_);
v___x_1354_ = v___x_1352_;
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_io_promise_resolve(v___x_1356_, v_val_1331_);
v___x_1358_ = l_IO_CancelToken_isSet(v_val_1342_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1360_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1356_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v___x_1362_; 
lean_del_object(v___x_1354_);
v___x_1362_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1362_;
}
}
}
else
{
return v___x_1352_;
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1378_; 
v_a_1365_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1367_ = v___x_1348_;
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1348_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_io_error_to_string(v_a_1365_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 3);
lean_ctor_set(v___x_1345_, 0, v___x_1369_);
v___x_1371_ = v___x_1345_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = l_Lean_MessageData_ofFormat(v___x_1371_);
lean_inc(v_ref_1341_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_ref_1341_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1373_);
v___x_1375_ = v___x_1367_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
else
{
return v___x_1343_;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1);
v___x_1382_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1381_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1383_, lean_object* v_x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(v_val_1383_, v_x_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v_val_1383_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(lean_object* v_x_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1));
v___x_1412_ = l_Lean_Syntax_isOfKind(v_x_1401_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___y_1420_; 
v___x_1414_ = lean_io_promise_new();
v___x_1415_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1416_ = lean_st_ref_take(v___x_1415_);
v___f_1417_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
lean_inc(v___x_1414_);
v___f_1418_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed), 9, 1);
lean_closure_set(v___f_1418_, 0, v___x_1414_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = l_IO_Promise_result_x21___redArg(v___x_1414_);
lean_dec(v___x_1414_);
v___y_1420_ = v___x_1458_;
goto v___jp_1419_;
}
else
{
lean_object* v_val_1459_; 
lean_dec(v___x_1414_);
v_val_1459_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1459_);
v___y_1420_ = v_val_1459_;
goto v___jp_1419_;
}
v___jp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___y_1420_);
v___x_1422_ = lean_st_ref_set(v___x_1415_, v___x_1421_);
if (lean_obj_tag(v___x_1416_) == 1)
{
lean_object* v_val_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___f_1418_);
v_val_1423_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1425_ = v___x_1416_;
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_val_1423_);
lean_dec(v___x_1416_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = lean_io_wait(v_val_1423_);
lean_dec(v___x_1427_);
v___x_1428_ = lean_box(0);
if (v_isShared_1426_ == 0)
{
lean_ctor_set_tag(v___x_1425_, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1428_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v___x_1416_);
v___x_1433_ = l_IO_CancelToken_new();
v___x_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
v___x_1435_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2));
v___x_1436_ = l_Lean_Name_toString(v___x_1435_, v___x_1412_);
lean_inc_ref(v___x_1434_);
v___x_1437_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1418_, v___x_1434_, v___x_1436_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_apply_1(v_a_1438_, v___x_1439_);
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_io_as_task(v___x_1440_, v___x_1441_);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
lean_ctor_set(v___x_1445_, 2, v___x_1434_);
lean_ctor_set(v___x_1445_, 3, v___x_1442_);
v___x_1446_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1445_, v_a_1409_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_8001__overap_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v___x_1446_);
v___x_1447_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_8001__overap_1448_ = lean_dbg_trace(v___x_1447_, v___f_1417_);
lean_inc(v_a_1409_);
lean_inc_ref(v_a_1408_);
lean_inc(v_a_1407_);
lean_inc_ref(v_a_1406_);
lean_inc(v_a_1405_);
lean_inc_ref(v_a_1404_);
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
v___x_1449_ = lean_apply_9(v___x_8001__overap_1448_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, lean_box(0));
return v___x_1449_;
}
else
{
return v___x_1446_;
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___x_1434_);
v_a_1450_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1437_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1437_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___boxed(lean_object* v_x_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(v_x_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(lean_object* v_val_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1471_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(lean_object* v_val_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(v_val_1481_, v_b_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v_val_1481_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(lean_object* v_val_1507_, lean_object* v_val_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1507_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v___x_1517_, 0);
lean_dec(v_unused_1560_);
v___x_1519_ = v___x_1517_;
v_isShared_1520_ = v_isSharedCheck_1559_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v___x_1517_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1559_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1522_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v___x_1522_);
lean_del_object(v___x_1519_);
v___x_1523_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1524_ = 2;
v___x_1525_ = 0;
v___x_1526_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1523_, v___x_1524_, v___x_1525_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1542_; 
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v___x_1526_, 0);
lean_dec(v_unused_1543_);
v___x_1528_ = v___x_1526_;
v_isShared_1529_ = v_isSharedCheck_1542_;
goto v_resetjp_1527_;
}
else
{
lean_dec(v___x_1526_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1542_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_cancelTk_x3f_1532_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_io_promise_resolve(v___x_1530_, v_val_1508_);
v_cancelTk_x3f_1532_ = lean_ctor_get(v___y_1514_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1532_) == 1)
{
lean_object* v_val_1533_; uint8_t v___x_1534_; 
v_val_1533_ = lean_ctor_get(v_cancelTk_x3f_1532_, 0);
v___x_1534_ = l_IO_CancelToken_isSet(v_val_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1536_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1536_ = v___x_1528_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1530_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
else
{
lean_object* v___x_1538_; 
lean_del_object(v___x_1528_);
v___x_1538_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1538_;
}
}
else
{
lean_object* v___x_1540_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1540_ = v___x_1528_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1530_);
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
return v___x_1526_;
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1558_; 
v_a_1544_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1546_ = v___x_1522_;
v_isShared_1547_ = v_isSharedCheck_1558_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1522_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1558_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_ref_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v_ref_1548_ = lean_ctor_get(v___y_1514_, 5);
v___x_1549_ = lean_io_error_to_string(v_a_1544_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 3);
lean_ctor_set(v___x_1519_, 0, v___x_1549_);
v___x_1551_ = v___x_1519_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1552_ = l_Lean_MessageData_ofFormat(v___x_1551_);
lean_inc(v_ref_1548_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_ref_1548_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1553_);
v___x_1555_ = v___x_1546_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
else
{
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1561_, lean_object* v_val_1562_, lean_object* v_x_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(v_val_1561_, v_val_1562_, v_x_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v_val_1562_);
lean_dec(v_val_1561_);
return v_res_1571_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1582_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1583_ = lean_unsigned_to_nat(60u);
v___x_1584_ = lean_unsigned_to_nat(169u);
v___x_1585_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3));
v___x_1586_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1587_ = l_mkPanicMessageWithDecl(v___x_1586_, v___x_1585_, v___x_1584_, v___x_1583_, v___x_1582_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(lean_object* v_x_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1));
v___x_1599_ = l_Lean_Syntax_isOfKind(v_x_1588_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___y_1606_; 
v___x_1601_ = lean_io_promise_new();
v___x_1602_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1603_ = lean_st_ref_take(v___x_1602_);
v___f_1604_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = l_IO_Promise_result_x21___redArg(v___x_1601_);
v___y_1606_ = v___x_1647_;
goto v___jp_1605_;
}
else
{
lean_object* v_val_1648_; 
v_val_1648_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_val_1648_);
v___y_1606_ = v_val_1648_;
goto v___jp_1605_;
}
v___jp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___y_1606_);
v___x_1608_ = lean_st_ref_set(v___x_1602_, v___x_1607_);
if (lean_obj_tag(v___x_1603_) == 1)
{
lean_object* v_val_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v___x_1601_);
v_val_1609_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1611_ = v___x_1603_;
v_isShared_1612_ = v_isSharedCheck_1618_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_val_1609_);
lean_dec(v___x_1603_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1618_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1613_ = lean_io_wait(v_val_1609_);
lean_dec(v___x_1613_);
v___x_1614_ = lean_box(0);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1614_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_cancelTk_x3f_1619_; 
lean_dec(v___x_1603_);
v_cancelTk_x3f_1619_ = lean_ctor_get(v_a_1595_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1619_) == 1)
{
lean_object* v_val_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_val_1620_ = lean_ctor_get(v_cancelTk_x3f_1619_, 0);
lean_inc(v_val_1620_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed), 10, 2);
lean_closure_set(v___f_1621_, 0, v_val_1620_);
lean_closure_set(v___f_1621_, 1, v___x_1601_);
v___x_1622_ = lean_box(0);
v___x_1623_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1));
v___x_1624_ = l_Lean_Name_toString(v___x_1623_, v___x_1599_);
v___x_1625_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1621_, v___x_1622_, v___x_1624_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_apply_1(v_a_1626_, v___x_1627_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_io_as_task(v___x_1628_, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_1619_);
v___x_1632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1622_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
lean_ctor_set(v___x_1632_, 2, v_cancelTk_x3f_1619_);
lean_ctor_set(v___x_1632_, 3, v___x_1630_);
v___x_1633_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1632_, v_a_1596_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; lean_object* v___x_7935__overap_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v___x_1633_);
v___x_1634_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_7935__overap_1635_ = lean_dbg_trace(v___x_1634_, v___f_1604_);
lean_inc(v_a_1596_);
lean_inc_ref(v_a_1595_);
lean_inc(v_a_1594_);
lean_inc_ref(v_a_1593_);
lean_inc(v_a_1592_);
lean_inc_ref(v_a_1591_);
lean_inc(v_a_1590_);
lean_inc_ref(v_a_1589_);
v___x_1636_ = lean_apply_9(v___x_7935__overap_1635_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, lean_box(0));
return v___x_1636_;
}
else
{
return v___x_1633_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_a_1637_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1625_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1625_);
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
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v___x_1601_);
v___x_1645_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4);
v___x_1646_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_1645_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___boxed(lean_object* v_x_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(v_x_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_st_mk_ref(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg(){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg___boxed(lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(lean_object* v_00_u03b1_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___boxed(lean_object* v_00_u03b1_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(v_00_u03b1_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(lean_object* v_msg_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___f_1713_; lean_object* v___x_4180__overap_1714_; lean_object* v___x_1715_; 
v___f_1713_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0));
v___x_4180__overap_1714_ = lean_panic_fn_borrowed(v___f_1713_, v_msg_1709_);
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
v___x_1715_ = lean_apply_3(v___x_4180__overap_1714_, v___y_1710_, v___y_1711_, lean_box(0));
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___boxed(lean_object* v_msg_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v_msg_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1720_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
lean_ctor_set(v___x_1726_, 2, v___x_1725_);
lean_ctor_set(v___x_1726_, 3, v___x_1725_);
lean_ctor_set(v___x_1726_, 4, v___x_1724_);
lean_ctor_set(v___x_1726_, 5, v___x_1724_);
lean_ctor_set(v___x_1726_, 6, v___x_1724_);
lean_ctor_set(v___x_1726_, 7, v___x_1724_);
lean_ctor_set(v___x_1726_, 8, v___x_1724_);
lean_ctor_set(v___x_1726_, 9, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_unsigned_to_nat(32u);
v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1730_ = ((size_t)5ULL);
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_unsigned_to_nat(32u);
v___x_1733_ = lean_mk_empty_array_with_capacity(v___x_1732_);
v___x_1734_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3);
v___x_1735_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v___x_1733_);
lean_ctor_set(v___x_1735_, 2, v___x_1731_);
lean_ctor_set(v___x_1735_, 3, v___x_1731_);
lean_ctor_set_usize(v___x_1735_, 4, v___x_1730_);
return v___x_1735_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1736_ = lean_box(1);
v___x_1737_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4);
v___x_1738_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1737_);
lean_ctor_set(v___x_1739_, 2, v___x_1736_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(lean_object* v_msgData_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v_env_1745_; lean_object* v_options_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1744_ = lean_st_ref_get(v___y_1742_);
v_env_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_ref(v_env_1745_);
lean_dec(v___x_1744_);
v_options_1746_ = lean_ctor_get(v___y_1741_, 2);
v___x_1747_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_1748_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5);
lean_inc_ref(v_options_1746_);
v___x_1749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1749_, 0, v_env_1745_);
lean_ctor_set(v___x_1749_, 1, v___x_1747_);
lean_ctor_set(v___x_1749_, 2, v___x_1748_);
lean_ctor_set(v___x_1749_, 3, v_options_1746_);
v___x_1750_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v_msgData_1740_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v_msgData_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(lean_object* v_ref_1757_, lean_object* v_msgData_1758_, uint8_t v_severity_1759_, uint8_t v_isSilent_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; uint8_t v___y_1804_; uint8_t v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; uint8_t v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; uint8_t v___y_1841_; uint8_t v___y_1842_; uint8_t v___y_1843_; uint8_t v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; uint8_t v___y_1854_; uint8_t v___y_1855_; uint8_t v___y_1856_; uint8_t v___y_1858_; uint8_t v___x_1873_; 
v___x_1848_ = 2;
v___x_1873_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1759_, v___x_1848_);
if (v___x_1873_ == 0)
{
v___y_1858_ = v___x_1873_;
goto v___jp_1857_;
}
else
{
uint8_t v___x_1874_; 
lean_inc_ref(v_msgData_1758_);
v___x_1874_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1758_);
v___y_1858_ = v___x_1874_;
goto v___jp_1857_;
}
v___jp_1764_:
{
lean_object* v___x_1774_; lean_object* v_currNamespace_1775_; lean_object* v_openDecls_1776_; lean_object* v_env_1777_; lean_object* v_nextMacroScope_1778_; lean_object* v_ngen_1779_; lean_object* v_auxDeclNGen_1780_; lean_object* v_traceState_1781_; lean_object* v_cache_1782_; lean_object* v_messages_1783_; lean_object* v_infoState_1784_; lean_object* v_snapshotTasks_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1799_; 
v___x_1774_ = lean_st_ref_take(v___y_1773_);
v_currNamespace_1775_ = lean_ctor_get(v___y_1772_, 6);
v_openDecls_1776_ = lean_ctor_get(v___y_1772_, 7);
v_env_1777_ = lean_ctor_get(v___x_1774_, 0);
v_nextMacroScope_1778_ = lean_ctor_get(v___x_1774_, 1);
v_ngen_1779_ = lean_ctor_get(v___x_1774_, 2);
v_auxDeclNGen_1780_ = lean_ctor_get(v___x_1774_, 3);
v_traceState_1781_ = lean_ctor_get(v___x_1774_, 4);
v_cache_1782_ = lean_ctor_get(v___x_1774_, 5);
v_messages_1783_ = lean_ctor_get(v___x_1774_, 6);
v_infoState_1784_ = lean_ctor_get(v___x_1774_, 7);
v_snapshotTasks_1785_ = lean_ctor_get(v___x_1774_, 8);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1787_ = v___x_1774_;
v_isShared_1788_ = v_isSharedCheck_1799_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_snapshotTasks_1785_);
lean_inc(v_infoState_1784_);
lean_inc(v_messages_1783_);
lean_inc(v_cache_1782_);
lean_inc(v_traceState_1781_);
lean_inc(v_auxDeclNGen_1780_);
lean_inc(v_ngen_1779_);
lean_inc(v_nextMacroScope_1778_);
lean_inc(v_env_1777_);
lean_dec(v___x_1774_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1799_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc(v_openDecls_1776_);
lean_inc(v_currNamespace_1775_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_currNamespace_1775_);
lean_ctor_set(v___x_1789_, 1, v_openDecls_1776_);
v___x_1790_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___y_1770_);
lean_inc_ref(v___y_1768_);
lean_inc_ref(v___y_1767_);
v___x_1791_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1791_, 0, v___y_1767_);
lean_ctor_set(v___x_1791_, 1, v___y_1766_);
lean_ctor_set(v___x_1791_, 2, v___y_1765_);
lean_ctor_set(v___x_1791_, 3, v___y_1768_);
lean_ctor_set(v___x_1791_, 4, v___x_1790_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*5, v___y_1769_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*5 + 1, v___y_1771_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*5 + 2, v_isSilent_1760_);
v___x_1792_ = l_Lean_MessageLog_add(v___x_1791_, v_messages_1783_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 6, v___x_1792_);
v___x_1794_ = v___x_1787_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_env_1777_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_nextMacroScope_1778_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_ngen_1779_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_auxDeclNGen_1780_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_traceState_1781_);
lean_ctor_set(v_reuseFailAlloc_1798_, 5, v_cache_1782_);
lean_ctor_set(v_reuseFailAlloc_1798_, 6, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 7, v_infoState_1784_);
lean_ctor_set(v_reuseFailAlloc_1798_, 8, v_snapshotTasks_1785_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_st_ref_set(v___y_1773_, v___x_1794_);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
v___jp_1800_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
v___x_1809_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1758_);
v___x_1810_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v___x_1809_, v___y_1761_, v___y_1762_);
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_inc_ref_n(v___y_1802_, 2);
v___x_1815_ = l_Lean_FileMap_toPosition(v___y_1802_, v___y_1806_);
lean_dec(v___y_1806_);
v___x_1816_ = l_Lean_FileMap_toPosition(v___y_1802_, v___y_1808_);
lean_dec(v___y_1808_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_1805_ == 0)
{
lean_del_object(v___x_1813_);
lean_dec_ref(v___y_1801_);
v___y_1765_ = v___x_1817_;
v___y_1766_ = v___x_1815_;
v___y_1767_ = v___y_1803_;
v___y_1768_ = v___x_1818_;
v___y_1769_ = v___y_1804_;
v___y_1770_ = v_a_1811_;
v___y_1771_ = v___y_1807_;
v___y_1772_ = v___y_1761_;
v___y_1773_ = v___y_1762_;
goto v___jp_1764_;
}
else
{
uint8_t v___x_1819_; 
lean_inc(v_a_1811_);
v___x_1819_ = l_Lean_MessageData_hasTag(v___y_1801_, v_a_1811_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___x_1815_);
lean_dec(v_a_1811_);
v___x_1820_ = lean_box(0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1820_);
v___x_1822_ = v___x_1813_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
lean_del_object(v___x_1813_);
v___y_1765_ = v___x_1817_;
v___y_1766_ = v___x_1815_;
v___y_1767_ = v___y_1803_;
v___y_1768_ = v___x_1818_;
v___y_1769_ = v___y_1804_;
v___y_1770_ = v_a_1811_;
v___y_1771_ = v___y_1807_;
v___y_1772_ = v___y_1761_;
v___y_1773_ = v___y_1762_;
goto v___jp_1764_;
}
}
}
}
v___jp_1825_:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Syntax_getTailPos_x3f(v___y_1828_, v___y_1830_);
lean_dec(v___y_1828_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_inc(v___y_1833_);
v___y_1801_ = v___y_1826_;
v___y_1802_ = v___y_1827_;
v___y_1803_ = v___y_1829_;
v___y_1804_ = v___y_1830_;
v___y_1805_ = v___y_1831_;
v___y_1806_ = v___y_1833_;
v___y_1807_ = v___y_1832_;
v___y_1808_ = v___y_1833_;
goto v___jp_1800_;
}
else
{
lean_object* v_val_1835_; 
v_val_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_val_1835_);
lean_dec_ref(v___x_1834_);
v___y_1801_ = v___y_1826_;
v___y_1802_ = v___y_1827_;
v___y_1803_ = v___y_1829_;
v___y_1804_ = v___y_1830_;
v___y_1805_ = v___y_1831_;
v___y_1806_ = v___y_1833_;
v___y_1807_ = v___y_1832_;
v___y_1808_ = v_val_1835_;
goto v___jp_1800_;
}
}
v___jp_1836_:
{
lean_object* v_ref_1844_; lean_object* v___x_1845_; 
v_ref_1844_ = l_Lean_replaceRef(v_ref_1757_, v___y_1840_);
v___x_1845_ = l_Lean_Syntax_getPos_x3f(v_ref_1844_, v___y_1841_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v___y_1826_ = v___y_1837_;
v___y_1827_ = v___y_1838_;
v___y_1828_ = v_ref_1844_;
v___y_1829_ = v___y_1839_;
v___y_1830_ = v___y_1841_;
v___y_1831_ = v___y_1842_;
v___y_1832_ = v___y_1843_;
v___y_1833_ = v___x_1846_;
goto v___jp_1825_;
}
else
{
lean_object* v_val_1847_; 
v_val_1847_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_val_1847_);
lean_dec_ref(v___x_1845_);
v___y_1826_ = v___y_1837_;
v___y_1827_ = v___y_1838_;
v___y_1828_ = v_ref_1844_;
v___y_1829_ = v___y_1839_;
v___y_1830_ = v___y_1841_;
v___y_1831_ = v___y_1842_;
v___y_1832_ = v___y_1843_;
v___y_1833_ = v_val_1847_;
goto v___jp_1825_;
}
}
v___jp_1849_:
{
if (v___y_1856_ == 0)
{
v___y_1837_ = v___y_1851_;
v___y_1838_ = v___y_1850_;
v___y_1839_ = v___y_1852_;
v___y_1840_ = v___y_1853_;
v___y_1841_ = v___y_1855_;
v___y_1842_ = v___y_1854_;
v___y_1843_ = v_severity_1759_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___y_1851_;
v___y_1838_ = v___y_1850_;
v___y_1839_ = v___y_1852_;
v___y_1840_ = v___y_1853_;
v___y_1841_ = v___y_1855_;
v___y_1842_ = v___y_1854_;
v___y_1843_ = v___x_1848_;
goto v___jp_1836_;
}
}
v___jp_1857_:
{
if (v___y_1858_ == 0)
{
lean_object* v_fileName_1859_; lean_object* v_fileMap_1860_; lean_object* v_options_1861_; lean_object* v_ref_1862_; uint8_t v_suppressElabErrors_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___f_1866_; uint8_t v___x_1867_; uint8_t v___x_1868_; 
v_fileName_1859_ = lean_ctor_get(v___y_1761_, 0);
v_fileMap_1860_ = lean_ctor_get(v___y_1761_, 1);
v_options_1861_ = lean_ctor_get(v___y_1761_, 2);
v_ref_1862_ = lean_ctor_get(v___y_1761_, 5);
v_suppressElabErrors_1863_ = lean_ctor_get_uint8(v___y_1761_, sizeof(void*)*14 + 1);
v___x_1864_ = lean_box(v___y_1858_);
v___x_1865_ = lean_box(v_suppressElabErrors_1863_);
v___f_1866_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1866_, 0, v___x_1864_);
lean_closure_set(v___f_1866_, 1, v___x_1865_);
v___x_1867_ = 1;
v___x_1868_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1759_, v___x_1867_);
if (v___x_1868_ == 0)
{
v___y_1850_ = v_fileMap_1860_;
v___y_1851_ = v___f_1866_;
v___y_1852_ = v_fileName_1859_;
v___y_1853_ = v_ref_1862_;
v___y_1854_ = v_suppressElabErrors_1863_;
v___y_1855_ = v___y_1858_;
v___y_1856_ = v___x_1868_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = l_Lean_warningAsError;
v___x_1870_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_1861_, v___x_1869_);
v___y_1850_ = v_fileMap_1860_;
v___y_1851_ = v___f_1866_;
v___y_1852_ = v_fileName_1859_;
v___y_1853_ = v_ref_1862_;
v___y_1854_ = v_suppressElabErrors_1863_;
v___y_1855_ = v___y_1858_;
v___y_1856_ = v___x_1870_;
goto v___jp_1849_;
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec_ref(v_msgData_1758_);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_1875_, lean_object* v_msgData_1876_, lean_object* v_severity_1877_, lean_object* v_isSilent_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v_severity_boxed_1882_; uint8_t v_isSilent_boxed_1883_; lean_object* v_res_1884_; 
v_severity_boxed_1882_ = lean_unbox(v_severity_1877_);
v_isSilent_boxed_1883_ = lean_unbox(v_isSilent_1878_);
v_res_1884_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1875_, v_msgData_1876_, v_severity_boxed_1882_, v_isSilent_boxed_1883_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v_ref_1875_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(lean_object* v_msgData_1885_, uint8_t v_severity_1886_, uint8_t v_isSilent_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_ref_1891_; lean_object* v___x_1892_; 
v_ref_1891_ = lean_ctor_get(v___y_1888_, 5);
v___x_1892_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1891_, v_msgData_1885_, v_severity_1886_, v_isSilent_1887_, v___y_1888_, v___y_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2___boxed(lean_object* v_msgData_1893_, lean_object* v_severity_1894_, lean_object* v_isSilent_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
uint8_t v_severity_boxed_1899_; uint8_t v_isSilent_boxed_1900_; lean_object* v_res_1901_; 
v_severity_boxed_1899_ = lean_unbox(v_severity_1894_);
v_isSilent_boxed_1900_ = lean_unbox(v_isSilent_1895_);
v_res_1901_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1893_, v_severity_boxed_1899_, v_isSilent_boxed_1900_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(lean_object* v_msgData_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
uint8_t v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = 0;
v___x_1907_ = 0;
v___x_1908_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1902_, v___x_1906_, v___x_1907_, v___y_1903_, v___y_1904_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2___boxed(lean_object* v_msgData_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v_msgData_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(lean_object* v_val_1914_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = l_IO_CancelToken_isSet(v_val_1914_);
if (v___x_1916_ == 0)
{
uint32_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = 30;
v___x_1918_ = l_IO_sleep(v___x_1917_);
goto _start;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(lean_object* v_val_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1922_);
lean_dec(v_val_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(lean_object* v_val_1925_, lean_object* v_val_1926_, lean_object* v_x_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1925_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1971_; 
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v___x_1931_, 0);
lean_dec(v_unused_1972_);
v___x_1933_ = v___x_1931_;
v_isShared_1934_ = v_isSharedCheck_1971_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v___x_1931_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1971_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1936_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1935_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec_ref(v___x_1936_);
lean_del_object(v___x_1933_);
v___x_1937_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1938_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_1937_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1954_; 
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1938_, 0);
lean_dec(v_unused_1955_);
v___x_1940_ = v___x_1938_;
v_isShared_1941_ = v_isSharedCheck_1954_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v___x_1938_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1954_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_cancelTk_x3f_1944_; 
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_io_promise_resolve(v___x_1942_, v_val_1926_);
v_cancelTk_x3f_1944_ = lean_ctor_get(v___y_1928_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1944_) == 1)
{
lean_object* v_val_1945_; uint8_t v___x_1946_; 
v_val_1945_ = lean_ctor_get(v_cancelTk_x3f_1944_, 0);
v___x_1946_ = l_IO_CancelToken_isSet(v_val_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1948_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1942_);
v___x_1948_ = v___x_1940_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1942_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
else
{
lean_object* v___x_1950_; 
lean_del_object(v___x_1940_);
v___x_1950_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1950_;
}
}
else
{
lean_object* v___x_1952_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1942_);
v___x_1952_ = v___x_1940_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1942_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
return v___x_1938_;
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1970_; 
v_a_1956_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1958_ = v___x_1936_;
v_isShared_1959_ = v_isSharedCheck_1970_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1936_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1970_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_ref_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v_ref_1960_ = lean_ctor_get(v___y_1928_, 5);
v___x_1961_ = lean_io_error_to_string(v_a_1956_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 3);
lean_ctor_set(v___x_1933_, 0, v___x_1961_);
v___x_1963_ = v___x_1933_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1964_ = l_Lean_MessageData_ofFormat(v___x_1963_);
lean_inc(v_ref_1960_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_ref_1960_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1965_);
v___x_1967_ = v___x_1958_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
else
{
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed(lean_object* v_val_1973_, lean_object* v_val_1974_, lean_object* v_x_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(v_val_1973_, v_val_1974_, v_x_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v_val_1974_);
lean_dec(v_val_1973_);
return v_res_1979_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1982_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1983_ = lean_unsigned_to_nat(44u);
v___x_1984_ = lean_unsigned_to_nat(201u);
v___x_1985_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1));
v___x_1986_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1987_ = l_mkPanicMessageWithDecl(v___x_1986_, v___x_1985_, v___x_1984_, v___x_1983_, v___x_1982_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v___x_1990_, lean_object* v___x_1991_, uint8_t v___x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___y_2000_; 
v___x_1996_ = lean_io_promise_new();
v___x_1997_ = l_Lean_Server_Test_Cancel_cmdOnceRef;
v___x_1998_ = lean_st_ref_take(v___x_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_2041_; 
v___x_2041_ = l_IO_Promise_result_x21___redArg(v___x_1996_);
v___y_2000_ = v___x_2041_;
goto v___jp_1999_;
}
else
{
lean_object* v_val_2042_; 
v_val_2042_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_val_2042_);
v___y_2000_ = v_val_2042_;
goto v___jp_1999_;
}
v___jp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___y_2000_);
v___x_2002_ = lean_st_ref_set(v___x_1997_, v___x_2001_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v___x_1996_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v___x_1990_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1988_);
v_val_2003_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2005_ = v___x_1998_;
v_isShared_2006_ = v_isSharedCheck_2012_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_dec(v___x_1998_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2012_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2007_ = lean_io_wait(v_val_2003_);
lean_dec(v___x_2007_);
v___x_2008_ = lean_box(0);
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2008_);
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_object* v_cancelTk_x3f_2013_; 
lean_dec(v___x_1998_);
v_cancelTk_x3f_2013_ = lean_ctor_get(v___y_1993_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2013_) == 1)
{
lean_object* v_val_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_val_2014_ = lean_ctor_get(v_cancelTk_x3f_2013_, 0);
lean_inc(v_val_2014_);
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_2015_, 0, v_val_2014_);
lean_closure_set(v___f_2015_, 1, v___x_1996_);
v___x_2016_ = lean_box(0);
v___x_2017_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0));
v___x_2018_ = l_Lean_Name_mkStr5(v___x_1988_, v___x_1989_, v___x_1990_, v___x_1991_, v___x_2017_);
v___x_2019_ = l_Lean_Name_toString(v___x_2018_, v___x_1992_);
v___x_2020_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_2015_, v___x_2016_, v___x_2019_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_apply_1(v_a_2021_, v___x_2022_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_io_as_task(v___x_2023_, v___x_2024_);
v___x_2026_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_2013_);
v___x_2027_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2016_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
lean_ctor_set(v___x_2027_, 2, v_cancelTk_x3f_2013_);
lean_ctor_set(v___x_2027_, 3, v___x_2025_);
v___x_2028_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2027_, v___y_1994_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec_ref(v___x_2028_);
v___x_2029_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_2030_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_2029_, v___y_1993_, v___y_1994_);
lean_dec_ref(v___y_1993_);
return v___x_2030_;
}
else
{
lean_dec_ref(v___y_1993_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v___y_1993_);
v_a_2031_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2020_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2020_);
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
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec(v___x_1996_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v___x_1990_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1988_);
v___x_2039_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2);
v___x_2040_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v___x_2039_, v___y_1993_, v___y_1994_);
lean_dec_ref(v___y_1993_);
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed(lean_object* v___x_2043_, lean_object* v___x_2044_, lean_object* v___x_2045_, lean_object* v___x_2046_, lean_object* v___x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v___x_7208__boxed_2051_; lean_object* v_res_2052_; 
v___x_7208__boxed_2051_ = lean_unbox(v___x_2047_);
v_res_2052_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(v___x_2043_, v___x_2044_, v___x_2045_, v___x_2046_, v___x_7208__boxed_2051_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(lean_object* v_x_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2057_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_2058_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_2059_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_2060_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_2061_ = ((lean_object*)(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1));
v___x_2062_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_box(v___x_2062_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2065_, 0, v___x_2057_);
lean_closure_set(v___f_2065_, 1, v___x_2058_);
lean_closure_set(v___f_2065_, 2, v___x_2059_);
lean_closure_set(v___f_2065_, 3, v___x_2060_);
lean_closure_set(v___f_2065_, 4, v___x_2064_);
v___x_2066_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_2065_, v_a_2054_, v_a_2055_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___boxed(lean_object* v_x_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(v_x_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(lean_object* v_val_2072_, lean_object* v_b_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_2072_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(lean_object* v_val_2078_, lean_object* v_b_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(v_val_2078_, v_b_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v_val_2078_);
return v_res_2083_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Test_Cancel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Test_Cancel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_onceRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_onceRef);
lean_dec_ref(res);
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_unblockedCancelTk = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_unblockedCancelTk);
lean_dec_ref(res);
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_cmdOnceRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_cmdOnceRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Test_Cancel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Test_Cancel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Test_Cancel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Test_Cancel(builtin);
}
#ifdef __cplusplus
}
#endif
