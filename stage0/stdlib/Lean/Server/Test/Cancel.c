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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot_default;
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2____boxed(lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
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
lean_object* v___f_86_; lean_object* v___x_10766__overap_87_; lean_object* v___x_88_; 
v___f_86_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0));
v___x_10766__overap_87_ = lean_panic_fn(v___f_86_, v_msg_76_);
v___x_88_ = lean_apply_9(v___x_10766__overap_87_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, lean_box(0));
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___boxed(lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
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
uint8_t v___y_14918__boxed_202_; uint8_t v_suppressElabErrors_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v___y_14918__boxed_202_ = lean_unbox(v___y_199_);
v_suppressElabErrors_boxed_203_ = lean_unbox(v_suppressElabErrors_200_);
v_res_204_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(v___y_14918__boxed_202_, v_suppressElabErrors_boxed_203_, v_x_201_);
lean_dec(v_x_201_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(lean_object* v_ref_207_, lean_object* v_msgData_208_, uint8_t v_severity_209_, uint8_t v_isSilent_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; uint8_t v___y_258_; uint8_t v___y_259_; lean_object* v___y_260_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; uint8_t v___y_282_; uint8_t v___y_283_; uint8_t v___y_284_; lean_object* v___y_285_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; uint8_t v___y_293_; uint8_t v___y_294_; uint8_t v___y_295_; uint8_t v___x_300_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; uint8_t v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; uint8_t v___y_310_; uint8_t v___x_325_; 
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
lean_inc(v_currNamespace_227_);
v_openDecls_228_ = lean_ctor_get(v___y_224_, 7);
lean_inc(v_openDecls_228_);
lean_dec_ref(v___y_224_);
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
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_currNamespace_227_);
lean_ctor_set(v___x_241_, 1, v_openDecls_228_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___y_220_);
v___x_243_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_243_, 0, v___y_219_);
lean_ctor_set(v___x_243_, 1, v___y_217_);
lean_ctor_set(v___x_243_, 2, v___y_218_);
lean_ctor_set(v___x_243_, 3, v___y_222_);
lean_ctor_set(v___x_243_, 4, v___x_242_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*5, v___y_223_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*5 + 1, v___y_221_);
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
lean_inc_ref(v___y_257_);
v___x_267_ = l_Lean_FileMap_toPosition(v___y_257_, v___y_255_);
lean_dec(v___y_255_);
v___x_268_ = l_Lean_FileMap_toPosition(v___y_257_, v___y_260_);
lean_dec(v___y_260_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_258_ == 0)
{
lean_del_object(v___x_265_);
lean_dec_ref(v___y_253_);
v___y_217_ = v___x_267_;
v___y_218_ = v___x_269_;
v___y_219_ = v___y_254_;
v___y_220_ = v_a_263_;
v___y_221_ = v___y_256_;
v___y_222_ = v___x_270_;
v___y_223_ = v___y_259_;
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
lean_dec_ref(v___y_254_);
lean_dec_ref(v___y_213_);
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
v___y_218_ = v___x_269_;
v___y_219_ = v___y_254_;
v___y_220_ = v_a_263_;
v___y_221_ = v___y_256_;
v___y_222_ = v___x_270_;
v___y_223_ = v___y_259_;
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
v___x_286_ = l_Lean_Syntax_getTailPos_x3f(v___y_279_, v___y_283_);
lean_dec(v___y_279_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_inc(v___y_285_);
v___y_253_ = v___y_278_;
v___y_254_ = v___y_280_;
v___y_255_ = v___y_285_;
v___y_256_ = v___y_282_;
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
v___y_254_ = v___y_280_;
v___y_255_ = v___y_285_;
v___y_256_ = v___y_282_;
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
v_ref_296_ = l_Lean_replaceRef(v_ref_207_, v___y_290_);
lean_dec(v___y_290_);
v___x_297_ = l_Lean_Syntax_getPos_x3f(v_ref_296_, v___y_294_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___y_278_ = v___y_289_;
v___y_279_ = v_ref_296_;
v___y_280_ = v___y_291_;
v___y_281_ = v___y_292_;
v___y_282_ = v___y_295_;
v___y_283_ = v___y_294_;
v___y_284_ = v___y_293_;
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
v___y_279_ = v_ref_296_;
v___y_280_ = v___y_291_;
v___y_281_ = v___y_292_;
v___y_282_ = v___y_295_;
v___y_283_ = v___y_294_;
v___y_284_ = v___y_293_;
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
v___y_292_ = v___y_305_;
v___y_293_ = v___y_306_;
v___y_294_ = v___y_307_;
v___y_295_ = v_severity_209_;
goto v___jp_288_;
}
else
{
v___y_289_ = v___y_302_;
v___y_290_ = v___y_303_;
v___y_291_ = v___y_304_;
v___y_292_ = v___y_305_;
v___y_293_ = v___y_306_;
v___y_294_ = v___y_307_;
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
lean_inc_ref(v_fileMap_312_);
lean_inc_ref(v_fileName_311_);
lean_inc(v_ref_314_);
v___y_302_ = v___f_318_;
v___y_303_ = v_ref_314_;
v___y_304_ = v_fileName_311_;
v___y_305_ = v_fileMap_312_;
v___y_306_ = v_suppressElabErrors_315_;
v___y_307_ = v___y_310_;
v___y_308_ = v___x_320_;
goto v___jp_301_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_warningAsError;
v___x_322_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_313_, v___x_321_);
lean_inc_ref(v_fileMap_312_);
lean_inc_ref(v_fileName_311_);
lean_inc(v_ref_314_);
v___y_302_ = v___f_318_;
v___y_303_ = v_ref_314_;
v___y_304_ = v_fileName_311_;
v___y_305_ = v_fileMap_312_;
v___y_306_ = v_suppressElabErrors_315_;
v___y_307_ = v___y_310_;
v___y_308_ = v___x_322_;
goto v___jp_301_;
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v___y_213_);
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
lean_inc(v_ref_351_);
v___x_352_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_351_, v_msgData_339_, v_severity_340_, v_isSilent_341_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v_ref_351_);
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
v___x_377_ = l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot_default;
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
lean_inc_ref(v___y_414_);
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
lean_inc(v_val_422_);
v___x_423_ = l_Lean_Core_getMessageLog___redArg(v___y_415_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; size_t v___x_429_; lean_object* v___x_430_; lean_object* v_new_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_490_; 
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
v_isSharedCheck_490_ = !lean_is_exclusive(v_val_422_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_val_422_, 0);
lean_dec(v_unused_491_);
v___x_433_ = v_val_422_;
v_isShared_434_ = v_isSharedCheck_490_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_new_431_);
lean_dec(v_val_422_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_490_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint64_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_cancelTk_x3f_447_; 
v___x_435_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4));
v___x_436_ = l_Lean_Name_mkStr5(v___x_401_, v___x_402_, v___x_403_, v___x_404_, v___x_435_);
v___x_437_ = l_Lean_Name_toString(v___x_436_, v___x_405_);
v___x_438_ = lean_box(0);
v___x_439_ = 0ULL;
v___x_440_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_440_, 0, v___x_430_);
lean_ctor_set_uint64(v___x_440_, sizeof(void*)*1, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_441_, 0, v___x_437_);
lean_ctor_set(v___x_441_, 1, v___x_425_);
lean_ctor_set(v___x_441_, 2, v___x_438_);
lean_ctor_set(v___x_441_, 3, v___x_440_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*4, v___x_419_);
v___x_442_ = lean_box(0);
v___x_443_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_400_);
lean_dec(v___x_400_);
v___x_445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_445_, 0, v___x_441_);
lean_ctor_set(v___x_445_, 1, v___x_442_);
lean_ctor_set(v___x_445_, 2, v___x_438_);
lean_ctor_set(v___x_445_, 3, v___x_443_);
lean_ctor_set(v___x_445_, 4, v___x_444_);
v___x_446_ = lean_io_promise_resolve(v___x_445_, v_new_431_);
lean_dec(v_new_431_);
v_cancelTk_x3f_447_ = lean_ctor_get(v___y_414_, 12);
if (lean_obj_tag(v_cancelTk_x3f_447_) == 1)
{
lean_object* v_ref_448_; lean_object* v_val_449_; lean_object* v___x_450_; 
v_ref_448_ = lean_ctor_get(v___y_414_, 5);
v_val_449_ = lean_ctor_get(v_cancelTk_x3f_447_, 0);
lean_inc(v_val_449_);
v___x_450_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_486_; 
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v___x_450_, 0);
lean_dec(v_unused_487_);
v___x_452_ = v___x_450_;
v_isShared_453_ = v_isSharedCheck_486_;
goto v_resetjp_451_;
}
else
{
lean_dec(v___x_450_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_486_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_455_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v___x_455_);
lean_del_object(v___x_452_);
lean_del_object(v___x_433_);
v___x_456_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_457_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_456_, v___x_418_, v___x_419_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_468_; 
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_469_);
v___x_459_ = v___x_457_;
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
else
{
lean_dec(v___x_457_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_io_promise_resolve(v___x_461_, v_val_406_);
v___x_463_ = l_IO_CancelToken_isSet(v_val_449_);
lean_dec(v_val_449_);
if (v___x_463_ == 0)
{
lean_object* v___x_465_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_465_ = v___x_459_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_461_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_object* v___x_467_; 
lean_del_object(v___x_459_);
v___x_467_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_467_;
}
}
}
else
{
lean_dec(v_val_449_);
return v___x_457_;
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_485_; 
lean_inc(v_ref_448_);
lean_dec(v_val_449_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
v_a_470_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_485_ == 0)
{
v___x_472_ = v___x_455_;
v_isShared_473_ = v_isSharedCheck_485_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_455_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_485_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_io_error_to_string(v_a_470_);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 3);
lean_ctor_set(v___x_452_, 0, v___x_474_);
v___x_476_ = v___x_452_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_484_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_MessageData_ofFormat(v___x_476_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_477_);
lean_ctor_set(v___x_433_, 0, v_ref_448_);
v___x_479_ = v___x_433_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_ref_448_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_479_);
v___x_481_ = v___x_472_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
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
}
}
}
else
{
lean_dec(v_val_449_);
lean_del_object(v___x_433_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v___x_450_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_del_object(v___x_433_);
v___x_488_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13);
v___x_489_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_488_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
return v___x_489_;
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_val_422_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_402_);
lean_dec_ref(v___x_401_);
lean_dec(v___x_400_);
v_a_492_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_423_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_423_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v___x_404_);
lean_dec_ref(v___x_403_);
lean_dec_ref(v___x_402_);
lean_dec_ref(v___x_401_);
lean_dec(v___x_400_);
v___x_500_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14);
v___x_501_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_500_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
return v___x_501_;
}
}
else
{
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
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
lean_object* v___x_502_ = _args[0];
lean_object* v___x_503_ = _args[1];
lean_object* v___x_504_ = _args[2];
lean_object* v___x_505_ = _args[3];
lean_object* v___x_506_ = _args[4];
lean_object* v___x_507_ = _args[5];
lean_object* v_val_508_ = _args[6];
lean_object* v_x_509_ = _args[7];
lean_object* v___y_510_ = _args[8];
lean_object* v___y_511_ = _args[9];
lean_object* v___y_512_ = _args[10];
lean_object* v___y_513_ = _args[11];
lean_object* v___y_514_ = _args[12];
lean_object* v___y_515_ = _args[13];
lean_object* v___y_516_ = _args[14];
lean_object* v___y_517_ = _args[15];
lean_object* v___y_518_ = _args[16];
_start:
{
uint8_t v___x_15298__boxed_519_; lean_object* v_res_520_; 
v___x_15298__boxed_519_ = lean_unbox(v___x_507_);
v_res_520_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(v___x_502_, v___x_503_, v___x_504_, v___x_505_, v___x_506_, v___x_15298__boxed_519_, v_val_508_, v_x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v_val_508_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(lean_object* v_x_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_532_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_533_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_534_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_535_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_536_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5));
v___x_537_ = l_Lean_Syntax_isOfKind(v_x_522_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
v___x_538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___f_544_; lean_object* v___y_546_; 
v___x_539_ = lean_io_promise_new();
v___x_540_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_541_ = lean_st_ref_take(v___x_540_);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_box(v___x_537_);
lean_inc(v___x_539_);
v___f_544_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed), 17, 7);
lean_closure_set(v___f_544_, 0, v___x_542_);
lean_closure_set(v___f_544_, 1, v___x_532_);
lean_closure_set(v___f_544_, 2, v___x_533_);
lean_closure_set(v___f_544_, 3, v___x_534_);
lean_closure_set(v___f_544_, 4, v___x_535_);
lean_closure_set(v___f_544_, 5, v___x_543_);
lean_closure_set(v___f_544_, 6, v___x_539_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_562_; 
v___x_562_ = l_IO_Promise_result_x21___redArg(v___x_539_);
lean_dec(v___x_539_);
v___y_546_ = v___x_562_;
goto v___jp_545_;
}
else
{
lean_object* v_val_563_; 
lean_dec(v___x_539_);
v_val_563_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_563_);
v___y_546_ = v_val_563_;
goto v___jp_545_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___y_546_);
v___x_548_ = lean_st_ref_set(v___x_540_, v___x_547_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
lean_dec_ref(v___f_544_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
v_val_549_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_558_ == 0)
{
v___x_551_ = v___x_541_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_dec(v___x_541_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = lean_io_wait(v_val_549_);
lean_dec(v___x_553_);
v___x_554_ = lean_box(0);
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 0);
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_9867__overap_560_; lean_object* v___x_561_; 
lean_dec(v___x_541_);
v___x_559_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_9867__overap_560_ = lean_dbg_trace(v___x_559_, v___f_544_);
v___x_561_ = lean_apply_9(v___x_9867__overap_560_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, lean_box(0));
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(lean_object* v_x_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(v_x_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(lean_object* v_val_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_575_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(lean_object* v_val_587_, lean_object* v_b_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(v_val_587_, v_b_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v_val_587_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(lean_object* v_ref_599_, lean_object* v_msgData_600_, uint8_t v_severity_601_, uint8_t v_isSilent_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_599_, v_msgData_600_, v_severity_601_, v_isSilent_602_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(lean_object* v_ref_613_, lean_object* v_msgData_614_, lean_object* v_severity_615_, lean_object* v_isSilent_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v_severity_boxed_626_; uint8_t v_isSilent_boxed_627_; lean_object* v_res_628_; 
v_severity_boxed_626_ = lean_unbox(v_severity_615_);
v_isSilent_boxed_627_ = lean_unbox(v_isSilent_616_);
v_res_628_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(v_ref_613_, v_msgData_614_, v_severity_boxed_626_, v_isSilent_boxed_627_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v_ref_613_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = l_IO_CancelToken_new();
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2____boxed(lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_();
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg(){
_start:
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = l_Lean_Server_Test_Cancel_unblockedCancelTk;
v___x_652_ = l_IO_CancelToken_isSet(v___x_651_);
if (v___x_652_ == 0)
{
uint32_t v___x_653_; lean_object* v___x_654_; 
v___x_653_ = 30;
v___x_654_ = l_IO_sleep(v___x_653_);
goto _start;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_box(0);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v_res_659_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_662_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_663_ = lean_unsigned_to_nat(37u);
v___x_664_ = lean_unsigned_to_nat(81u);
v___x_665_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_666_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_667_ = l_mkPanicMessageWithDecl(v___x_666_, v___x_665_, v___x_664_, v___x_663_, v___x_662_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, uint8_t v___x_673_, lean_object* v_val_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_686_ = 2;
v___x_687_ = 0;
lean_inc_ref(v___y_682_);
v___x_688_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_685_, v___x_686_, v___x_687_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_tacSnap_x3f_689_; 
lean_dec_ref(v___x_688_);
v_tacSnap_x3f_689_ = lean_ctor_get(v___y_678_, 6);
lean_inc(v_tacSnap_x3f_689_);
if (lean_obj_tag(v_tacSnap_x3f_689_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_760_; 
v_val_690_ = lean_ctor_get(v_tacSnap_x3f_689_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_tacSnap_x3f_689_);
if (v_isSharedCheck_760_ == 0)
{
v___x_692_ = v_tacSnap_x3f_689_;
v_isShared_693_ = v_isSharedCheck_760_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v_tacSnap_x3f_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_760_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Core_getMessageLog___redArg(v___y_683_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v_new_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_750_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v___x_696_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_695_);
v___x_697_ = lean_unsigned_to_nat(32u);
v___x_698_ = lean_mk_empty_array_with_capacity(v___x_697_);
v___x_699_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_700_ = ((size_t)5ULL);
lean_inc_n(v___x_668_, 2);
v___x_701_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_698_);
lean_ctor_set(v___x_701_, 2, v___x_668_);
lean_ctor_set(v___x_701_, 3, v___x_668_);
lean_ctor_set_usize(v___x_701_, 4, v___x_700_);
v_new_702_ = lean_ctor_get(v_val_690_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_val_690_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v_val_690_, 0);
lean_dec(v_unused_751_);
v___x_704_ = v_val_690_;
v_isShared_705_ = v_isSharedCheck_750_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_new_702_);
lean_dec(v_val_690_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_750_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint64_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_706_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0));
v___x_707_ = l_Lean_Name_mkStr5(v___x_669_, v___x_670_, v___x_671_, v___x_672_, v___x_706_);
v___x_708_ = l_Lean_Name_toString(v___x_707_, v___x_673_);
v___x_709_ = lean_box(0);
v___x_710_ = 0ULL;
v___x_711_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_711_, 0, v___x_701_);
lean_ctor_set_uint64(v___x_711_, sizeof(void*)*1, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_712_, 0, v___x_708_);
lean_ctor_set(v___x_712_, 1, v___x_696_);
lean_ctor_set(v___x_712_, 2, v___x_709_);
lean_ctor_set(v___x_712_, 3, v___x_711_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*4, v___x_687_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5);
v___x_715_ = lean_mk_empty_array_with_capacity(v___x_668_);
lean_dec(v___x_668_);
v___x_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_716_, 0, v___x_712_);
lean_ctor_set(v___x_716_, 1, v___x_713_);
lean_ctor_set(v___x_716_, 2, v___x_709_);
lean_ctor_set(v___x_716_, 3, v___x_714_);
lean_ctor_set(v___x_716_, 4, v___x_715_);
v___x_717_ = lean_io_promise_resolve(v___x_716_, v_new_702_);
lean_dec(v_new_702_);
v___x_718_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_748_; 
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_749_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_748_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_748_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
uint8_t v___x_722_; 
v___x_722_ = l_IO_CancelToken_isSet(v_val_674_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_del_object(v___x_704_);
lean_del_object(v___x_692_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
v___x_723_ = lean_box(0);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_del_object(v___x_720_);
v___x_727_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_728_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_727_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v___x_728_);
lean_del_object(v___x_704_);
lean_del_object(v___x_692_);
v___x_729_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_730_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_729_, v___x_686_, v___x_687_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v___x_730_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___y_683_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
v_a_731_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_747_ == 0)
{
v___x_733_ = v___x_728_;
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_728_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_747_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_ref_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v_ref_735_ = lean_ctor_get(v___y_682_, 5);
lean_inc(v_ref_735_);
lean_dec_ref(v___y_682_);
v___x_736_ = lean_io_error_to_string(v_a_731_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 3);
lean_ctor_set(v___x_692_, 0, v___x_736_);
v___x_738_ = v___x_692_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_746_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_739_);
lean_ctor_set(v___x_704_, 0, v_ref_735_);
v___x_741_ = v___x_704_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_ref_735_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_741_);
v___x_743_ = v___x_733_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
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
}
}
}
}
else
{
lean_del_object(v___x_704_);
lean_del_object(v___x_692_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v___x_718_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_del_object(v___x_692_);
lean_dec(v_val_690_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec(v___x_668_);
v_a_752_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_694_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_694_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v_tacSnap_x3f_689_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec(v___x_668_);
v___x_761_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2);
v___x_762_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_761_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v___x_762_;
}
}
else
{
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v___x_669_);
lean_dec(v___x_668_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_763_ = _args[0];
lean_object* v___x_764_ = _args[1];
lean_object* v___x_765_ = _args[2];
lean_object* v___x_766_ = _args[3];
lean_object* v___x_767_ = _args[4];
lean_object* v___x_768_ = _args[5];
lean_object* v_val_769_ = _args[6];
lean_object* v_x_770_ = _args[7];
lean_object* v___y_771_ = _args[8];
lean_object* v___y_772_ = _args[9];
lean_object* v___y_773_ = _args[10];
lean_object* v___y_774_ = _args[11];
lean_object* v___y_775_ = _args[12];
lean_object* v___y_776_ = _args[13];
lean_object* v___y_777_ = _args[14];
lean_object* v___y_778_ = _args[15];
lean_object* v___y_779_ = _args[16];
_start:
{
uint8_t v___x_6618__boxed_780_; lean_object* v_res_781_; 
v___x_6618__boxed_780_ = lean_unbox(v___x_768_);
v_res_781_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(v___x_763_, v___x_764_, v___x_765_, v___x_766_, v___x_767_, v___x_6618__boxed_780_, v_val_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v_val_769_);
return v_res_781_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_783_ = lean_unsigned_to_nat(39u);
v___x_784_ = lean_unsigned_to_nat(76u);
v___x_785_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_786_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_787_ = l_mkPanicMessageWithDecl(v___x_786_, v___x_785_, v___x_784_, v___x_783_, v___x_782_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(lean_object* v_x_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_798_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_799_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_800_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_801_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_802_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1));
v___x_803_ = l_Lean_Syntax_isOfKind(v_x_788_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
v___x_804_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_804_;
}
else
{
lean_object* v_cancelTk_x3f_805_; 
v_cancelTk_x3f_805_ = lean_ctor_get(v_a_795_, 12);
if (lean_obj_tag(v_cancelTk_x3f_805_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_5974__overap_811_; lean_object* v___x_812_; 
v_val_806_ = lean_ctor_get(v_cancelTk_x3f_805_, 0);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_box(v___x_803_);
lean_inc(v_val_806_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed), 17, 7);
lean_closure_set(v___f_809_, 0, v___x_807_);
lean_closure_set(v___f_809_, 1, v___x_798_);
lean_closure_set(v___f_809_, 2, v___x_799_);
lean_closure_set(v___f_809_, 3, v___x_800_);
lean_closure_set(v___f_809_, 4, v___x_801_);
lean_closure_set(v___f_809_, 5, v___x_808_);
lean_closure_set(v___f_809_, 6, v_val_806_);
v___x_810_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_5974__overap_811_ = lean_dbg_trace(v___x_810_, v___f_809_);
v___x_812_ = lean_apply_9(v___x_5974__overap_811_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, lean_box(0));
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0);
v___x_814_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_813_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(lean_object* v_x_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(v_x_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_847_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(lean_object* v_msg_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_5447__overap_874_; lean_object* v___x_875_; 
v___x_873_ = lean_obj_once(&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0, &l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0);
v___x_5447__overap_874_ = lean_panic_fn(v___x_873_, v_msg_865_);
v___x_875_ = lean_apply_7(v___x_5447__overap_874_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, lean_box(0));
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___boxed(lean_object* v_msg_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v_msg_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg(){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = l_Lean_Server_Test_Cancel_unblockedCancelTk;
v___x_887_ = l_IO_CancelToken_isSet(v___x_886_);
if (v___x_887_ == 0)
{
uint32_t v___x_888_; lean_object* v___x_889_; 
v___x_888_ = 30;
v___x_889_ = l_IO_sleep(v___x_888_);
goto _start;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(lean_object* v_ref_895_, lean_object* v_msgData_896_, uint8_t v_severity_897_, uint8_t v_isSilent_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; uint8_t v___y_909_; lean_object* v___y_910_; uint8_t v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_941_; uint8_t v___y_942_; lean_object* v___y_943_; uint8_t v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; uint8_t v___y_947_; lean_object* v___y_948_; lean_object* v___y_966_; uint8_t v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; uint8_t v___y_970_; lean_object* v___y_971_; uint8_t v___y_972_; lean_object* v___y_973_; lean_object* v___y_977_; uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; uint8_t v___y_982_; uint8_t v___y_983_; uint8_t v___x_988_; uint8_t v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; uint8_t v___y_996_; uint8_t v___y_998_; uint8_t v___x_1013_; 
v___x_988_ = 2;
v___x_1013_ = l_Lean_instBEqMessageSeverity_beq(v_severity_897_, v___x_988_);
if (v___x_1013_ == 0)
{
v___y_998_ = v___x_1013_;
goto v___jp_997_;
}
else
{
uint8_t v___x_1014_; 
lean_inc_ref(v_msgData_896_);
v___x_1014_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_896_);
v___y_998_ = v___x_1014_;
goto v___jp_997_;
}
v___jp_904_:
{
lean_object* v___x_914_; lean_object* v_currNamespace_915_; lean_object* v_openDecls_916_; lean_object* v_env_917_; lean_object* v_nextMacroScope_918_; lean_object* v_ngen_919_; lean_object* v_auxDeclNGen_920_; lean_object* v_traceState_921_; lean_object* v_cache_922_; lean_object* v_messages_923_; lean_object* v_infoState_924_; lean_object* v_snapshotTasks_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_939_; 
v___x_914_ = lean_st_ref_take(v___y_913_);
v_currNamespace_915_ = lean_ctor_get(v___y_912_, 6);
lean_inc(v_currNamespace_915_);
v_openDecls_916_ = lean_ctor_get(v___y_912_, 7);
lean_inc(v_openDecls_916_);
lean_dec_ref(v___y_912_);
v_env_917_ = lean_ctor_get(v___x_914_, 0);
v_nextMacroScope_918_ = lean_ctor_get(v___x_914_, 1);
v_ngen_919_ = lean_ctor_get(v___x_914_, 2);
v_auxDeclNGen_920_ = lean_ctor_get(v___x_914_, 3);
v_traceState_921_ = lean_ctor_get(v___x_914_, 4);
v_cache_922_ = lean_ctor_get(v___x_914_, 5);
v_messages_923_ = lean_ctor_get(v___x_914_, 6);
v_infoState_924_ = lean_ctor_get(v___x_914_, 7);
v_snapshotTasks_925_ = lean_ctor_get(v___x_914_, 8);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_939_ == 0)
{
v___x_927_ = v___x_914_;
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snapshotTasks_925_);
lean_inc(v_infoState_924_);
lean_inc(v_messages_923_);
lean_inc(v_cache_922_);
lean_inc(v_traceState_921_);
lean_inc(v_auxDeclNGen_920_);
lean_inc(v_ngen_919_);
lean_inc(v_nextMacroScope_918_);
lean_inc(v_env_917_);
lean_dec(v___x_914_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_currNamespace_915_);
lean_ctor_set(v___x_929_, 1, v_openDecls_916_);
v___x_930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___y_910_);
v___x_931_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_931_, 0, v___y_907_);
lean_ctor_set(v___x_931_, 1, v___y_908_);
lean_ctor_set(v___x_931_, 2, v___y_905_);
lean_ctor_set(v___x_931_, 3, v___y_906_);
lean_ctor_set(v___x_931_, 4, v___x_930_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*5, v___y_911_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*5 + 1, v___y_909_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*5 + 2, v_isSilent_898_);
v___x_932_ = l_Lean_MessageLog_add(v___x_931_, v_messages_923_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 6, v___x_932_);
v___x_934_ = v___x_927_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_env_917_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_nextMacroScope_918_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_ngen_919_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_auxDeclNGen_920_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_traceState_921_);
lean_ctor_set(v_reuseFailAlloc_938_, 5, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_938_, 6, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_938_, 7, v_infoState_924_);
lean_ctor_set(v_reuseFailAlloc_938_, 8, v_snapshotTasks_925_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_st_ref_set(v___y_913_, v___x_934_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
v___jp_940_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_964_; 
v___x_949_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_896_);
v___x_950_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_949_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_964_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_964_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_964_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc_ref(v___y_946_);
v___x_955_ = l_Lean_FileMap_toPosition(v___y_946_, v___y_945_);
lean_dec(v___y_945_);
v___x_956_ = l_Lean_FileMap_toPosition(v___y_946_, v___y_948_);
lean_dec(v___y_948_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_942_ == 0)
{
lean_del_object(v___x_953_);
lean_dec_ref(v___y_941_);
v___y_905_ = v___x_957_;
v___y_906_ = v___x_958_;
v___y_907_ = v___y_943_;
v___y_908_ = v___x_955_;
v___y_909_ = v___y_944_;
v___y_910_ = v_a_951_;
v___y_911_ = v___y_947_;
v___y_912_ = v___y_901_;
v___y_913_ = v___y_902_;
goto v___jp_904_;
}
else
{
uint8_t v___x_959_; 
lean_inc(v_a_951_);
v___x_959_ = l_Lean_MessageData_hasTag(v___y_941_, v_a_951_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_955_);
lean_dec(v_a_951_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v___y_901_);
v___x_960_ = lean_box(0);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_960_);
v___x_962_ = v___x_953_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_del_object(v___x_953_);
v___y_905_ = v___x_957_;
v___y_906_ = v___x_958_;
v___y_907_ = v___y_943_;
v___y_908_ = v___x_955_;
v___y_909_ = v___y_944_;
v___y_910_ = v_a_951_;
v___y_911_ = v___y_947_;
v___y_912_ = v___y_901_;
v___y_913_ = v___y_902_;
goto v___jp_904_;
}
}
}
}
v___jp_965_:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Syntax_getTailPos_x3f(v___y_968_, v___y_972_);
lean_dec(v___y_968_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_inc(v___y_973_);
v___y_941_ = v___y_966_;
v___y_942_ = v___y_967_;
v___y_943_ = v___y_969_;
v___y_944_ = v___y_970_;
v___y_945_ = v___y_973_;
v___y_946_ = v___y_971_;
v___y_947_ = v___y_972_;
v___y_948_ = v___y_973_;
goto v___jp_940_;
}
else
{
lean_object* v_val_975_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref(v___x_974_);
v___y_941_ = v___y_966_;
v___y_942_ = v___y_967_;
v___y_943_ = v___y_969_;
v___y_944_ = v___y_970_;
v___y_945_ = v___y_973_;
v___y_946_ = v___y_971_;
v___y_947_ = v___y_972_;
v___y_948_ = v_val_975_;
goto v___jp_940_;
}
}
v___jp_976_:
{
lean_object* v_ref_984_; lean_object* v___x_985_; 
v_ref_984_ = l_Lean_replaceRef(v_ref_895_, v___y_979_);
lean_dec(v___y_979_);
v___x_985_ = l_Lean_Syntax_getPos_x3f(v_ref_984_, v___y_982_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_unsigned_to_nat(0u);
v___y_966_ = v___y_977_;
v___y_967_ = v___y_978_;
v___y_968_ = v_ref_984_;
v___y_969_ = v___y_980_;
v___y_970_ = v___y_983_;
v___y_971_ = v___y_981_;
v___y_972_ = v___y_982_;
v___y_973_ = v___x_986_;
goto v___jp_965_;
}
else
{
lean_object* v_val_987_; 
v_val_987_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_987_);
lean_dec_ref(v___x_985_);
v___y_966_ = v___y_977_;
v___y_967_ = v___y_978_;
v___y_968_ = v_ref_984_;
v___y_969_ = v___y_980_;
v___y_970_ = v___y_983_;
v___y_971_ = v___y_981_;
v___y_972_ = v___y_982_;
v___y_973_ = v_val_987_;
goto v___jp_965_;
}
}
v___jp_989_:
{
if (v___y_996_ == 0)
{
v___y_977_ = v___y_993_;
v___y_978_ = v___y_990_;
v___y_979_ = v___y_991_;
v___y_980_ = v___y_992_;
v___y_981_ = v___y_994_;
v___y_982_ = v___y_995_;
v___y_983_ = v_severity_897_;
goto v___jp_976_;
}
else
{
v___y_977_ = v___y_993_;
v___y_978_ = v___y_990_;
v___y_979_ = v___y_991_;
v___y_980_ = v___y_992_;
v___y_981_ = v___y_994_;
v___y_982_ = v___y_995_;
v___y_983_ = v___x_988_;
goto v___jp_976_;
}
}
v___jp_997_:
{
if (v___y_998_ == 0)
{
lean_object* v_fileName_999_; lean_object* v_fileMap_1000_; lean_object* v_options_1001_; lean_object* v_ref_1002_; uint8_t v_suppressElabErrors_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; uint8_t v___x_1007_; uint8_t v___x_1008_; 
v_fileName_999_ = lean_ctor_get(v___y_901_, 0);
v_fileMap_1000_ = lean_ctor_get(v___y_901_, 1);
v_options_1001_ = lean_ctor_get(v___y_901_, 2);
v_ref_1002_ = lean_ctor_get(v___y_901_, 5);
v_suppressElabErrors_1003_ = lean_ctor_get_uint8(v___y_901_, sizeof(void*)*14 + 1);
v___x_1004_ = lean_box(v___y_998_);
v___x_1005_ = lean_box(v_suppressElabErrors_1003_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1006_, 0, v___x_1004_);
lean_closure_set(v___f_1006_, 1, v___x_1005_);
v___x_1007_ = 1;
v___x_1008_ = l_Lean_instBEqMessageSeverity_beq(v_severity_897_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_inc_ref(v_fileMap_1000_);
lean_inc_ref(v_fileName_999_);
lean_inc(v_ref_1002_);
v___y_990_ = v_suppressElabErrors_1003_;
v___y_991_ = v_ref_1002_;
v___y_992_ = v_fileName_999_;
v___y_993_ = v___f_1006_;
v___y_994_ = v_fileMap_1000_;
v___y_995_ = v___y_998_;
v___y_996_ = v___x_1008_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = l_Lean_warningAsError;
v___x_1010_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_1001_, v___x_1009_);
lean_inc_ref(v_fileMap_1000_);
lean_inc_ref(v_fileName_999_);
lean_inc(v_ref_1002_);
v___y_990_ = v_suppressElabErrors_1003_;
v___y_991_ = v_ref_1002_;
v___y_992_ = v_fileName_999_;
v___y_993_ = v___f_1006_;
v___y_994_ = v_fileMap_1000_;
v___y_995_ = v___y_998_;
v___y_996_ = v___x_1010_;
goto v___jp_989_;
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v___y_901_);
lean_dec_ref(v_msgData_896_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_1015_, lean_object* v_msgData_1016_, lean_object* v_severity_1017_, lean_object* v_isSilent_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v_severity_boxed_1024_; uint8_t v_isSilent_boxed_1025_; lean_object* v_res_1026_; 
v_severity_boxed_1024_ = lean_unbox(v_severity_1017_);
v_isSilent_boxed_1025_ = lean_unbox(v_isSilent_1018_);
v_res_1026_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1015_, v_msgData_1016_, v_severity_boxed_1024_, v_isSilent_boxed_1025_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v_ref_1015_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(lean_object* v_msgData_1027_, uint8_t v_severity_1028_, uint8_t v_isSilent_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_ref_1037_; lean_object* v___x_1038_; 
v_ref_1037_ = lean_ctor_get(v___y_1034_, 5);
lean_inc(v_ref_1037_);
v___x_1038_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1037_, v_msgData_1027_, v_severity_1028_, v_isSilent_1029_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v_ref_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(lean_object* v_msgData_1039_, lean_object* v_severity_1040_, lean_object* v_isSilent_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v_severity_boxed_1049_; uint8_t v_isSilent_boxed_1050_; lean_object* v_res_1051_; 
v_severity_boxed_1049_ = lean_unbox(v_severity_1040_);
v_isSilent_boxed_1050_ = lean_unbox(v_isSilent_1041_);
v_res_1051_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v_msgData_1039_, v_severity_boxed_1049_, v_isSilent_boxed_1050_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1053_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1054_ = lean_unsigned_to_nat(41u);
v___x_1055_ = lean_unsigned_to_nat(105u);
v___x_1056_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0));
v___x_1057_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1058_ = l_mkPanicMessageWithDecl(v___x_1057_, v___x_1056_, v___x_1055_, v___x_1054_, v___x_1053_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(lean_object* v_x_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_cancelTk_x3f_1067_; 
v_cancelTk_x3f_1067_ = lean_ctor_get(v___y_1064_, 12);
lean_inc(v_cancelTk_x3f_1067_);
if (lean_obj_tag(v_cancelTk_x3f_1067_) == 1)
{
lean_object* v_ref_1068_; lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1104_; 
v_ref_1068_ = lean_ctor_get(v___y_1064_, 5);
v_val_1069_ = lean_ctor_get(v_cancelTk_x3f_1067_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_cancelTk_x3f_1067_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1071_ = v_cancelTk_x3f_1067_;
v_isShared_1072_ = v_isSharedCheck_1104_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v_cancelTk_x3f_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1104_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1102_; 
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1103_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1102_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1102_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
uint8_t v___x_1077_; 
v___x_1077_ = l_IO_CancelToken_isSet(v_val_1069_);
lean_dec(v_val_1069_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_del_object(v___x_1071_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
v___x_1078_ = lean_box(0);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_del_object(v___x_1075_);
v___x_1082_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1083_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; uint8_t v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref(v___x_1083_);
lean_del_object(v___x_1071_);
v___x_1084_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1085_ = 2;
v___x_1086_ = 0;
v___x_1087_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1084_, v___x_1085_, v___x_1086_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v___x_1087_;
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
lean_inc(v_ref_1068_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
v_a_1088_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1090_ = v___x_1083_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1083_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_io_error_to_string(v_a_1088_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 3);
lean_ctor_set(v___x_1071_, 0, v___x_1092_);
v___x_1094_ = v___x_1071_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1095_ = l_Lean_MessageData_ofFormat(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_ref_1068_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1096_);
v___x_1098_ = v___x_1090_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1071_);
lean_dec(v_val_1069_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v___x_1073_;
}
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_cancelTk_x3f_1067_);
v___x_1105_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1);
v___x_1106_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1105_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed(lean_object* v_x_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(v_x_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v_res_1115_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(lean_object* v_x_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1));
v___x_1137_ = l_Lean_Syntax_isOfKind(v_x_1126_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_a_1131_);
lean_dec_ref(v_a_1129_);
v___x_1138_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = l_IO_CancelToken_new();
v___f_1140_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0));
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
v___x_1142_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2));
v___x_1143_ = l_Lean_Name_toString(v___x_1142_, v___x_1137_);
lean_inc_ref(v_a_1133_);
lean_inc_ref(v_a_1131_);
lean_inc_ref(v_a_1129_);
lean_inc_ref(v___x_1141_);
v___x_1144_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1140_, v___x_1141_, v___x_1143_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_apply_1(v_a_1145_, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_io_as_task(v___x_1147_, v___x_1148_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
lean_ctor_set(v___x_1152_, 2, v___x_1141_);
lean_ctor_set(v___x_1152_, 3, v___x_1149_);
v___x_1153_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1152_, v_a_1134_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1154_; uint8_t v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v___x_1153_);
v___x_1154_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1155_ = 2;
v___x_1156_ = 0;
v___x_1157_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1154_, v___x_1155_, v___x_1156_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec_ref(v_a_1131_);
lean_dec_ref(v_a_1129_);
return v___x_1157_;
}
else
{
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_a_1131_);
lean_dec_ref(v_a_1129_);
return v___x_1153_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_a_1131_);
lean_dec_ref(v_a_1129_);
v_a_1158_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1144_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1144_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___boxed(lean_object* v_x_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(v_x_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec(v_a_1172_);
lean_dec(v_a_1170_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_object* v_b_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(v_b_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(lean_object* v_ref_1195_, lean_object* v_msgData_1196_, uint8_t v_severity_1197_, uint8_t v_isSilent_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1195_, v_msgData_1196_, v_severity_1197_, v_isSilent_1198_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___boxed(lean_object* v_ref_1207_, lean_object* v_msgData_1208_, lean_object* v_severity_1209_, lean_object* v_isSilent_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_severity_boxed_1218_; uint8_t v_isSilent_boxed_1219_; lean_object* v_res_1220_; 
v_severity_boxed_1218_ = lean_unbox(v_severity_1209_);
v_isSilent_boxed_1219_ = lean_unbox(v_isSilent_1210_);
v_res_1220_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(v_ref_1207_, v_msgData_1208_, v_severity_boxed_1218_, v_isSilent_boxed_1219_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v_ref_1207_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = l_Lean_Server_Test_Cancel_unblockedCancelTk;
v___x_1248_ = l_IO_CancelToken_set(v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed(lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(v_x_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(lean_object* v_x_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1));
v___x_1274_ = l_Lean_Syntax_isOfKind(v_x_1263_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
v___x_1275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1275_;
}
else
{
lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_434__overap_1278_; lean_object* v___x_1279_; 
v___f_1276_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0));
v___x_1277_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1));
v___x_434__overap_1278_ = lean_dbg_trace(v___x_1277_, v___f_1276_);
v___x_1279_ = lean_apply_9(v___x_434__overap_1278_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, lean_box(0));
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___boxed(lean_object* v_x_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(v_x_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(lean_object* v_x_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1318_ = 2;
v___x_1319_ = 0;
v___x_1320_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1317_, v___x_1318_, v___x_1319_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed(lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(lean_object* v_val_1332_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = l_IO_CancelToken_isSet(v_val_1332_);
if (v___x_1334_ == 0)
{
uint32_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = 30;
v___x_1336_ = l_IO_sleep(v___x_1335_);
goto _start;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(lean_object* v_val_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1340_);
lean_dec(v_val_1340_);
return v_res_1342_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1344_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1345_ = lean_unsigned_to_nat(41u);
v___x_1346_ = lean_unsigned_to_nat(139u);
v___x_1347_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0));
v___x_1348_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1349_ = l_mkPanicMessageWithDecl(v___x_1348_, v___x_1347_, v___x_1346_, v___x_1345_, v___x_1344_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(lean_object* v_val_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_cancelTk_x3f_1359_; 
v_cancelTk_x3f_1359_ = lean_ctor_get(v___y_1356_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1359_) == 1)
{
lean_object* v_ref_1360_; lean_object* v_val_1361_; lean_object* v___x_1362_; 
v_ref_1360_ = lean_ctor_get(v___y_1356_, 5);
v_val_1361_ = lean_ctor_get(v_cancelTk_x3f_1359_, 0);
lean_inc(v_val_1361_);
v___x_1362_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1399_);
v___x_1364_ = v___x_1362_;
v_isShared_1365_ = v_isSharedCheck_1398_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v___x_1362_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1398_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1367_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v___x_1367_);
lean_del_object(v___x_1364_);
v___x_1368_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1369_ = 2;
v___x_1370_ = 0;
v___x_1371_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1368_, v___x_1369_, v___x_1370_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1382_; 
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1371_, 0);
lean_dec(v_unused_1383_);
v___x_1373_ = v___x_1371_;
v_isShared_1374_ = v_isSharedCheck_1382_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v___x_1371_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1382_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_io_promise_resolve(v___x_1375_, v_val_1350_);
v___x_1377_ = l_IO_CancelToken_isSet(v_val_1361_);
lean_dec(v_val_1361_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1379_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1379_ = v___x_1373_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1375_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v___x_1381_; 
lean_del_object(v___x_1373_);
v___x_1381_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1381_;
}
}
}
else
{
lean_dec(v_val_1361_);
return v___x_1371_;
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
lean_inc(v_ref_1360_);
lean_dec(v_val_1361_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
v_a_1384_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1386_ = v___x_1367_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1367_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_io_error_to_string(v_a_1384_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set_tag(v___x_1364_, 3);
lean_ctor_set(v___x_1364_, 0, v___x_1388_);
v___x_1390_ = v___x_1364_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = l_Lean_MessageData_ofFormat(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_ref_1360_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1392_);
v___x_1394_ = v___x_1386_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1361_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v___x_1362_;
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1);
v___x_1401_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1400_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1402_, lean_object* v_x_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(v_val_1402_, v_x_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v_val_1402_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1));
v___x_1431_ = l_Lean_Syntax_isOfKind(v_x_1420_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
v___x_1432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___y_1439_; 
v___x_1433_ = lean_io_promise_new();
v___x_1434_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1435_ = lean_st_ref_take(v___x_1434_);
v___f_1436_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
lean_inc(v___x_1433_);
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed), 9, 1);
lean_closure_set(v___f_1437_, 0, v___x_1433_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = l_IO_Promise_result_x21___redArg(v___x_1433_);
lean_dec(v___x_1433_);
v___y_1439_ = v___x_1477_;
goto v___jp_1438_;
}
else
{
lean_object* v_val_1478_; 
lean_dec(v___x_1433_);
v_val_1478_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1478_);
v___y_1439_ = v_val_1478_;
goto v___jp_1438_;
}
v___jp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1439_);
v___x_1441_ = lean_st_ref_set(v___x_1434_, v___x_1440_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v___f_1437_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
v_val_1442_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1444_ = v___x_1435_;
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_val_1442_);
lean_dec(v___x_1435_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1446_ = lean_io_wait(v_val_1442_);
lean_dec(v___x_1446_);
v___x_1447_ = lean_box(0);
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1447_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v___x_1435_);
v___x_1452_ = l_IO_CancelToken_new();
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2));
v___x_1455_ = l_Lean_Name_toString(v___x_1454_, v___x_1431_);
lean_inc_ref(v_a_1427_);
lean_inc_ref(v_a_1425_);
lean_inc_ref(v_a_1423_);
lean_inc_ref(v___x_1453_);
v___x_1456_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1437_, v___x_1453_, v___x_1455_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_apply_1(v_a_1457_, v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_io_as_task(v___x_1459_, v___x_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_ctor_set(v___x_1464_, 2, v___x_1453_);
lean_ctor_set(v___x_1464_, 3, v___x_1461_);
v___x_1465_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1464_, v_a_1428_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_8499__overap_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v___x_1465_);
v___x_1466_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_8499__overap_1467_ = lean_dbg_trace(v___x_1466_, v___f_1436_);
v___x_1468_ = lean_apply_9(v___x_8499__overap_1467_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, lean_box(0));
return v___x_1468_;
}
else
{
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
return v___x_1465_;
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v___x_1453_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
v_a_1469_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1456_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1456_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___boxed(lean_object* v_x_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(v_x_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(lean_object* v_val_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1490_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(lean_object* v_val_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(v_val_1500_, v_b_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v_val_1500_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(lean_object* v_val_1526_, lean_object* v_val_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1526_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1578_; 
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v___x_1536_, 0);
lean_dec(v_unused_1579_);
v___x_1538_ = v___x_1536_;
v_isShared_1539_ = v_isSharedCheck_1578_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v___x_1536_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1578_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1541_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1540_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; uint8_t v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v___x_1541_);
lean_del_object(v___x_1538_);
v___x_1542_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
v___x_1543_ = 2;
v___x_1544_ = 0;
lean_inc_ref(v___y_1533_);
v___x_1545_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1542_, v___x_1543_, v___x_1544_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1561_; 
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1562_);
v___x_1547_ = v___x_1545_;
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_cancelTk_x3f_1551_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_io_promise_resolve(v___x_1549_, v_val_1527_);
v_cancelTk_x3f_1551_ = lean_ctor_get(v___y_1533_, 12);
lean_inc(v_cancelTk_x3f_1551_);
lean_dec_ref(v___y_1533_);
if (lean_obj_tag(v_cancelTk_x3f_1551_) == 1)
{
lean_object* v_val_1552_; uint8_t v___x_1553_; 
v_val_1552_ = lean_ctor_get(v_cancelTk_x3f_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref(v_cancelTk_x3f_1551_);
v___x_1553_ = l_IO_CancelToken_isSet(v_val_1552_);
lean_dec(v_val_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1555_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1555_ = v___x_1547_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1549_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
else
{
lean_object* v___x_1557_; 
lean_del_object(v___x_1547_);
v___x_1557_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1557_;
}
}
else
{
lean_object* v___x_1559_; 
lean_dec(v_cancelTk_x3f_1551_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1559_ = v___x_1547_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1549_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_dec_ref(v___y_1533_);
return v___x_1545_;
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1577_; 
v_a_1563_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1565_ = v___x_1541_;
v_isShared_1566_ = v_isSharedCheck_1577_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1541_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1577_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v_ref_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v_ref_1567_ = lean_ctor_get(v___y_1533_, 5);
lean_inc(v_ref_1567_);
lean_dec_ref(v___y_1533_);
v___x_1568_ = lean_io_error_to_string(v_a_1563_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 3);
lean_ctor_set(v___x_1538_, 0, v___x_1568_);
v___x_1570_ = v___x_1538_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = l_Lean_MessageData_ofFormat(v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_ref_1567_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1572_);
v___x_1574_ = v___x_1565_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1533_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1580_, lean_object* v_val_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(v_val_1580_, v_val_1581_, v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v_val_1581_);
lean_dec(v_val_1580_);
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1601_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_1602_ = lean_unsigned_to_nat(60u);
v___x_1603_ = lean_unsigned_to_nat(169u);
v___x_1604_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3));
v___x_1605_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_1606_ = l_mkPanicMessageWithDecl(v___x_1605_, v___x_1604_, v___x_1603_, v___x_1602_, v___x_1601_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(lean_object* v_x_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1));
v___x_1618_ = l_Lean_Syntax_isOfKind(v_x_1607_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
v___x_1619_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v___y_1625_; 
v___x_1620_ = lean_io_promise_new();
v___x_1621_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1622_ = lean_st_ref_take(v___x_1621_);
v___f_1623_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = l_IO_Promise_result_x21___redArg(v___x_1620_);
v___y_1625_ = v___x_1666_;
goto v___jp_1624_;
}
else
{
lean_object* v_val_1667_; 
v_val_1667_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1667_);
v___y_1625_ = v_val_1667_;
goto v___jp_1624_;
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___y_1625_);
v___x_1627_ = lean_st_ref_set(v___x_1621_, v___x_1626_);
if (lean_obj_tag(v___x_1622_) == 1)
{
lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v___x_1620_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
v_val_1628_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1630_ = v___x_1622_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v___x_1622_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1632_ = lean_io_wait(v_val_1628_);
lean_dec(v___x_1632_);
v___x_1633_ = lean_box(0);
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1633_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v_cancelTk_x3f_1638_; 
lean_dec(v___x_1622_);
v_cancelTk_x3f_1638_ = lean_ctor_get(v_a_1614_, 12);
if (lean_obj_tag(v_cancelTk_x3f_1638_) == 1)
{
lean_object* v_val_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_val_1639_ = lean_ctor_get(v_cancelTk_x3f_1638_, 0);
lean_inc(v_val_1639_);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed), 10, 2);
lean_closure_set(v___f_1640_, 0, v_val_1639_);
lean_closure_set(v___f_1640_, 1, v___x_1620_);
v___x_1641_ = lean_box(0);
v___x_1642_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1));
v___x_1643_ = l_Lean_Name_toString(v___x_1642_, v___x_1618_);
lean_inc_ref(v_a_1614_);
lean_inc_ref(v_a_1612_);
lean_inc_ref(v_a_1610_);
v___x_1644_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1640_, v___x_1641_, v___x_1643_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1644_);
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_apply_1(v_a_1645_, v___x_1646_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_io_as_task(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_1638_);
v___x_1651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1641_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
lean_ctor_set(v___x_1651_, 2, v_cancelTk_x3f_1638_);
lean_ctor_set(v___x_1651_, 3, v___x_1649_);
v___x_1652_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1651_, v_a_1615_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; lean_object* v___x_8408__overap_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v___x_1652_);
v___x_1653_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_8408__overap_1654_ = lean_dbg_trace(v___x_1653_, v___f_1623_);
v___x_1655_ = lean_apply_9(v___x_8408__overap_1654_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, lean_box(0));
return v___x_1655_;
}
else
{
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
return v___x_1652_;
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
v_a_1656_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1644_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1644_);
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
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1620_);
v___x_1664_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4);
v___x_1665_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_1664_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___boxed(lean_object* v_x_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(v_x_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_st_mk_ref(v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg(){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg___boxed(lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(lean_object* v_00_u03b1_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___boxed(lean_object* v_00_u03b1_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(v_00_u03b1_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(lean_object* v_msg_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___f_1732_; lean_object* v___x_4793__overap_1733_; lean_object* v___x_1734_; 
v___f_1732_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0));
v___x_4793__overap_1733_ = lean_panic_fn(v___f_1732_, v_msg_1728_);
v___x_1734_ = lean_apply_3(v___x_4793__overap_1733_, v___y_1729_, v___y_1730_, lean_box(0));
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___boxed(lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v_msg_1735_, v___y_1736_, v___y_1737_);
return v_res_1739_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1740_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
lean_ctor_set(v___x_1745_, 2, v___x_1744_);
lean_ctor_set(v___x_1745_, 3, v___x_1743_);
lean_ctor_set(v___x_1745_, 4, v___x_1743_);
lean_ctor_set(v___x_1745_, 5, v___x_1743_);
lean_ctor_set(v___x_1745_, 6, v___x_1743_);
lean_ctor_set(v___x_1745_, 7, v___x_1743_);
lean_ctor_set(v___x_1745_, 8, v___x_1743_);
return v___x_1745_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_unsigned_to_nat(32u);
v___x_1747_ = lean_mk_empty_array_with_capacity(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
size_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1749_ = ((size_t)5ULL);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_unsigned_to_nat(32u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3);
v___x_1754_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___x_1752_);
lean_ctor_set(v___x_1754_, 2, v___x_1750_);
lean_ctor_set(v___x_1754_, 3, v___x_1750_);
lean_ctor_set_usize(v___x_1754_, 4, v___x_1749_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = lean_box(1);
v___x_1756_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4);
v___x_1757_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1756_);
lean_ctor_set(v___x_1758_, 2, v___x_1755_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(lean_object* v_msgData_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v_env_1764_; lean_object* v_options_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1763_ = lean_st_ref_get(v___y_1761_);
v_env_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc_ref(v_env_1764_);
lean_dec(v___x_1763_);
v_options_1765_ = lean_ctor_get(v___y_1760_, 2);
v___x_1766_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_1767_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5);
lean_inc_ref(v_options_1765_);
v___x_1768_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1768_, 0, v_env_1764_);
lean_ctor_set(v___x_1768_, 1, v___x_1766_);
lean_ctor_set(v___x_1768_, 2, v___x_1767_);
lean_ctor_set(v___x_1768_, 3, v_options_1765_);
v___x_1769_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v_msgData_1759_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v_msgData_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(lean_object* v_ref_1776_, lean_object* v_msgData_1777_, uint8_t v_severity_1778_, uint8_t v_isSilent_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; uint8_t v___y_1787_; uint8_t v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1848_; uint8_t v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1856_; lean_object* v___y_1857_; uint8_t v___y_1858_; uint8_t v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1862_; uint8_t v___x_1867_; lean_object* v___y_1869_; lean_object* v___y_1870_; uint8_t v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; uint8_t v___y_1874_; uint8_t v___y_1875_; uint8_t v___y_1877_; uint8_t v___x_1892_; 
v___x_1867_ = 2;
v___x_1892_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1778_, v___x_1867_);
if (v___x_1892_ == 0)
{
v___y_1877_ = v___x_1892_;
goto v___jp_1876_;
}
else
{
uint8_t v___x_1893_; 
lean_inc_ref(v_msgData_1777_);
v___x_1893_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1777_);
v___y_1877_ = v___x_1893_;
goto v___jp_1876_;
}
v___jp_1783_:
{
lean_object* v___x_1793_; lean_object* v_currNamespace_1794_; lean_object* v_openDecls_1795_; lean_object* v_env_1796_; lean_object* v_nextMacroScope_1797_; lean_object* v_ngen_1798_; lean_object* v_auxDeclNGen_1799_; lean_object* v_traceState_1800_; lean_object* v_cache_1801_; lean_object* v_messages_1802_; lean_object* v_infoState_1803_; lean_object* v_snapshotTasks_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1818_; 
v___x_1793_ = lean_st_ref_take(v___y_1792_);
v_currNamespace_1794_ = lean_ctor_get(v___y_1791_, 6);
lean_inc(v_currNamespace_1794_);
v_openDecls_1795_ = lean_ctor_get(v___y_1791_, 7);
lean_inc(v_openDecls_1795_);
lean_dec_ref(v___y_1791_);
v_env_1796_ = lean_ctor_get(v___x_1793_, 0);
v_nextMacroScope_1797_ = lean_ctor_get(v___x_1793_, 1);
v_ngen_1798_ = lean_ctor_get(v___x_1793_, 2);
v_auxDeclNGen_1799_ = lean_ctor_get(v___x_1793_, 3);
v_traceState_1800_ = lean_ctor_get(v___x_1793_, 4);
v_cache_1801_ = lean_ctor_get(v___x_1793_, 5);
v_messages_1802_ = lean_ctor_get(v___x_1793_, 6);
v_infoState_1803_ = lean_ctor_get(v___x_1793_, 7);
v_snapshotTasks_1804_ = lean_ctor_get(v___x_1793_, 8);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1806_ = v___x_1793_;
v_isShared_1807_ = v_isSharedCheck_1818_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snapshotTasks_1804_);
lean_inc(v_infoState_1803_);
lean_inc(v_messages_1802_);
lean_inc(v_cache_1801_);
lean_inc(v_traceState_1800_);
lean_inc(v_auxDeclNGen_1799_);
lean_inc(v_ngen_1798_);
lean_inc(v_nextMacroScope_1797_);
lean_inc(v_env_1796_);
lean_dec(v___x_1793_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1818_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_currNamespace_1794_);
lean_ctor_set(v___x_1808_, 1, v_openDecls_1795_);
v___x_1809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___y_1784_);
v___x_1810_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1810_, 0, v___y_1790_);
lean_ctor_set(v___x_1810_, 1, v___y_1786_);
lean_ctor_set(v___x_1810_, 2, v___y_1785_);
lean_ctor_set(v___x_1810_, 3, v___y_1789_);
lean_ctor_set(v___x_1810_, 4, v___x_1809_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*5, v___y_1787_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*5 + 1, v___y_1788_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*5 + 2, v_isSilent_1779_);
v___x_1811_ = l_Lean_MessageLog_add(v___x_1810_, v_messages_1802_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 6, v___x_1811_);
v___x_1813_ = v___x_1806_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_env_1796_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_nextMacroScope_1797_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_ngen_1798_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_auxDeclNGen_1799_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_traceState_1800_);
lean_ctor_set(v_reuseFailAlloc_1817_, 5, v_cache_1801_);
lean_ctor_set(v_reuseFailAlloc_1817_, 6, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1817_, 7, v_infoState_1803_);
lean_ctor_set(v_reuseFailAlloc_1817_, 8, v_snapshotTasks_1804_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_st_ref_set(v___y_1792_, v___x_1813_);
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
v___jp_1819_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1843_; 
v___x_1828_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1777_);
v___x_1829_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v___x_1828_, v___y_1780_, v___y_1781_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_inc_ref(v___y_1821_);
v___x_1834_ = l_Lean_FileMap_toPosition(v___y_1821_, v___y_1826_);
lean_dec(v___y_1826_);
v___x_1835_ = l_Lean_FileMap_toPosition(v___y_1821_, v___y_1827_);
lean_dec(v___y_1827_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_1822_ == 0)
{
lean_del_object(v___x_1832_);
lean_dec_ref(v___y_1820_);
v___y_1784_ = v_a_1830_;
v___y_1785_ = v___x_1836_;
v___y_1786_ = v___x_1834_;
v___y_1787_ = v___y_1823_;
v___y_1788_ = v___y_1824_;
v___y_1789_ = v___x_1837_;
v___y_1790_ = v___y_1825_;
v___y_1791_ = v___y_1780_;
v___y_1792_ = v___y_1781_;
goto v___jp_1783_;
}
else
{
uint8_t v___x_1838_; 
lean_inc(v_a_1830_);
v___x_1838_ = l_Lean_MessageData_hasTag(v___y_1820_, v_a_1830_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec_ref(v___x_1836_);
lean_dec_ref(v___x_1834_);
lean_dec(v_a_1830_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v___y_1780_);
v___x_1839_ = lean_box(0);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
else
{
lean_del_object(v___x_1832_);
v___y_1784_ = v_a_1830_;
v___y_1785_ = v___x_1836_;
v___y_1786_ = v___x_1834_;
v___y_1787_ = v___y_1823_;
v___y_1788_ = v___y_1824_;
v___y_1789_ = v___x_1837_;
v___y_1790_ = v___y_1825_;
v___y_1791_ = v___y_1780_;
v___y_1792_ = v___y_1781_;
goto v___jp_1783_;
}
}
}
}
v___jp_1844_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Syntax_getTailPos_x3f(v___y_1846_, v___y_1849_);
lean_dec(v___y_1846_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_inc(v___y_1852_);
v___y_1820_ = v___y_1845_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1848_;
v___y_1823_ = v___y_1849_;
v___y_1824_ = v___y_1850_;
v___y_1825_ = v___y_1851_;
v___y_1826_ = v___y_1852_;
v___y_1827_ = v___y_1852_;
goto v___jp_1819_;
}
else
{
lean_object* v_val_1854_; 
v_val_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_val_1854_);
lean_dec_ref(v___x_1853_);
v___y_1820_ = v___y_1845_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1848_;
v___y_1823_ = v___y_1849_;
v___y_1824_ = v___y_1850_;
v___y_1825_ = v___y_1851_;
v___y_1826_ = v___y_1852_;
v___y_1827_ = v_val_1854_;
goto v___jp_1819_;
}
}
v___jp_1855_:
{
lean_object* v_ref_1863_; lean_object* v___x_1864_; 
v_ref_1863_ = l_Lean_replaceRef(v_ref_1776_, v___y_1861_);
lean_dec(v___y_1861_);
v___x_1864_ = l_Lean_Syntax_getPos_x3f(v_ref_1863_, v___y_1859_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___y_1845_ = v___y_1856_;
v___y_1846_ = v_ref_1863_;
v___y_1847_ = v___y_1857_;
v___y_1848_ = v___y_1858_;
v___y_1849_ = v___y_1859_;
v___y_1850_ = v___y_1862_;
v___y_1851_ = v___y_1860_;
v___y_1852_ = v___x_1865_;
goto v___jp_1844_;
}
else
{
lean_object* v_val_1866_; 
v_val_1866_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_val_1866_);
lean_dec_ref(v___x_1864_);
v___y_1845_ = v___y_1856_;
v___y_1846_ = v_ref_1863_;
v___y_1847_ = v___y_1857_;
v___y_1848_ = v___y_1858_;
v___y_1849_ = v___y_1859_;
v___y_1850_ = v___y_1862_;
v___y_1851_ = v___y_1860_;
v___y_1852_ = v_val_1866_;
goto v___jp_1844_;
}
}
v___jp_1868_:
{
if (v___y_1875_ == 0)
{
v___y_1856_ = v___y_1870_;
v___y_1857_ = v___y_1869_;
v___y_1858_ = v___y_1871_;
v___y_1859_ = v___y_1874_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1873_;
v___y_1862_ = v_severity_1778_;
goto v___jp_1855_;
}
else
{
v___y_1856_ = v___y_1870_;
v___y_1857_ = v___y_1869_;
v___y_1858_ = v___y_1871_;
v___y_1859_ = v___y_1874_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1873_;
v___y_1862_ = v___x_1867_;
goto v___jp_1855_;
}
}
v___jp_1876_:
{
if (v___y_1877_ == 0)
{
lean_object* v_fileName_1878_; lean_object* v_fileMap_1879_; lean_object* v_options_1880_; lean_object* v_ref_1881_; uint8_t v_suppressElabErrors_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___f_1885_; uint8_t v___x_1886_; uint8_t v___x_1887_; 
v_fileName_1878_ = lean_ctor_get(v___y_1780_, 0);
v_fileMap_1879_ = lean_ctor_get(v___y_1780_, 1);
v_options_1880_ = lean_ctor_get(v___y_1780_, 2);
v_ref_1881_ = lean_ctor_get(v___y_1780_, 5);
v_suppressElabErrors_1882_ = lean_ctor_get_uint8(v___y_1780_, sizeof(void*)*14 + 1);
v___x_1883_ = lean_box(v___y_1877_);
v___x_1884_ = lean_box(v_suppressElabErrors_1882_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1885_, 0, v___x_1883_);
lean_closure_set(v___f_1885_, 1, v___x_1884_);
v___x_1886_ = 1;
v___x_1887_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1778_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_inc(v_ref_1881_);
lean_inc_ref(v_fileName_1878_);
lean_inc_ref(v_fileMap_1879_);
v___y_1869_ = v_fileMap_1879_;
v___y_1870_ = v___f_1885_;
v___y_1871_ = v_suppressElabErrors_1882_;
v___y_1872_ = v_fileName_1878_;
v___y_1873_ = v_ref_1881_;
v___y_1874_ = v___y_1877_;
v___y_1875_ = v___x_1887_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = l_Lean_warningAsError;
v___x_1889_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_1880_, v___x_1888_);
lean_inc(v_ref_1881_);
lean_inc_ref(v_fileName_1878_);
lean_inc_ref(v_fileMap_1879_);
v___y_1869_ = v_fileMap_1879_;
v___y_1870_ = v___f_1885_;
v___y_1871_ = v_suppressElabErrors_1882_;
v___y_1872_ = v_fileName_1878_;
v___y_1873_ = v_ref_1881_;
v___y_1874_ = v___y_1877_;
v___y_1875_ = v___x_1889_;
goto v___jp_1868_;
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_msgData_1777_);
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_1894_, lean_object* v_msgData_1895_, lean_object* v_severity_1896_, lean_object* v_isSilent_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v_severity_boxed_1901_; uint8_t v_isSilent_boxed_1902_; lean_object* v_res_1903_; 
v_severity_boxed_1901_ = lean_unbox(v_severity_1896_);
v_isSilent_boxed_1902_ = lean_unbox(v_isSilent_1897_);
v_res_1903_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1894_, v_msgData_1895_, v_severity_boxed_1901_, v_isSilent_boxed_1902_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec(v_ref_1894_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(lean_object* v_msgData_1904_, uint8_t v_severity_1905_, uint8_t v_isSilent_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_ref_1910_; lean_object* v___x_1911_; 
v_ref_1910_ = lean_ctor_get(v___y_1907_, 5);
lean_inc(v_ref_1910_);
v___x_1911_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1910_, v_msgData_1904_, v_severity_1905_, v_isSilent_1906_, v___y_1907_, v___y_1908_);
lean_dec(v_ref_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2___boxed(lean_object* v_msgData_1912_, lean_object* v_severity_1913_, lean_object* v_isSilent_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
uint8_t v_severity_boxed_1918_; uint8_t v_isSilent_boxed_1919_; lean_object* v_res_1920_; 
v_severity_boxed_1918_ = lean_unbox(v_severity_1913_);
v_isSilent_boxed_1919_ = lean_unbox(v_isSilent_1914_);
v_res_1920_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1912_, v_severity_boxed_1918_, v_isSilent_boxed_1919_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(lean_object* v_msgData_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
uint8_t v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = 0;
v___x_1926_ = 0;
v___x_1927_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1921_, v___x_1925_, v___x_1926_, v___y_1922_, v___y_1923_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2___boxed(lean_object* v_msgData_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v_msgData_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(lean_object* v_val_1933_){
_start:
{
uint8_t v___x_1935_; 
v___x_1935_ = l_IO_CancelToken_isSet(v_val_1933_);
if (v___x_1935_ == 0)
{
uint32_t v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = 30;
v___x_1937_ = l_IO_sleep(v___x_1936_);
goto _start;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(lean_object* v_val_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1941_);
lean_dec(v_val_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(lean_object* v_val_1944_, lean_object* v_val_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1944_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1990_; 
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1950_, 0);
lean_dec(v_unused_1991_);
v___x_1952_ = v___x_1950_;
v_isShared_1953_ = v_isSharedCheck_1990_;
goto v_resetjp_1951_;
}
else
{
lean_dec(v___x_1950_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1990_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6));
v___x_1955_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1952_);
v___x_1956_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
lean_inc_ref(v___y_1947_);
v___x_1957_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_1956_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1973_; 
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1974_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1973_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1973_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_cancelTk_x3f_1963_; 
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_io_promise_resolve(v___x_1961_, v_val_1945_);
v_cancelTk_x3f_1963_ = lean_ctor_get(v___y_1947_, 12);
lean_inc(v_cancelTk_x3f_1963_);
lean_dec_ref(v___y_1947_);
if (lean_obj_tag(v_cancelTk_x3f_1963_) == 1)
{
lean_object* v_val_1964_; uint8_t v___x_1965_; 
v_val_1964_ = lean_ctor_get(v_cancelTk_x3f_1963_, 0);
lean_inc(v_val_1964_);
lean_dec_ref(v_cancelTk_x3f_1963_);
v___x_1965_ = l_IO_CancelToken_isSet(v_val_1964_);
lean_dec(v_val_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1967_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1967_ = v___x_1959_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1961_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
else
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1959_);
v___x_1969_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1969_;
}
}
else
{
lean_object* v___x_1971_; 
lean_dec(v_cancelTk_x3f_1963_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1971_ = v___x_1959_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1961_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_dec_ref(v___y_1947_);
return v___x_1957_;
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1989_; 
v_a_1975_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1977_ = v___x_1955_;
v_isShared_1978_ = v_isSharedCheck_1989_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1955_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1989_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_ref_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v_ref_1979_ = lean_ctor_get(v___y_1947_, 5);
lean_inc(v_ref_1979_);
lean_dec_ref(v___y_1947_);
v___x_1980_ = lean_io_error_to_string(v_a_1975_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 3);
lean_ctor_set(v___x_1952_, 0, v___x_1980_);
v___x_1982_ = v___x_1952_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1983_ = l_Lean_MessageData_ofFormat(v___x_1982_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_ref_1979_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1984_);
v___x_1986_ = v___x_1977_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1947_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed(lean_object* v_val_1992_, lean_object* v_val_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(v_val_1992_, v_val_1993_, v_x_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec(v_val_1993_);
lean_dec(v_val_1992_);
return v_res_1998_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2001_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12));
v___x_2002_ = lean_unsigned_to_nat(44u);
v___x_2003_ = lean_unsigned_to_nat(201u);
v___x_2004_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1));
v___x_2005_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_2006_ = l_mkPanicMessageWithDecl(v___x_2005_, v___x_2004_, v___x_2003_, v___x_2002_, v___x_2001_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(lean_object* v___x_2007_, lean_object* v___x_2008_, lean_object* v___x_2009_, lean_object* v___x_2010_, uint8_t v___x_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___y_2019_; 
v___x_2015_ = lean_io_promise_new();
v___x_2016_ = l_Lean_Server_Test_Cancel_cmdOnceRef;
v___x_2017_ = lean_st_ref_take(v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2060_; 
v___x_2060_ = l_IO_Promise_result_x21___redArg(v___x_2015_);
v___y_2019_ = v___x_2060_;
goto v___jp_2018_;
}
else
{
lean_object* v_val_2061_; 
v_val_2061_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2061_);
v___y_2019_ = v_val_2061_;
goto v___jp_2018_;
}
v___jp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2019_);
v___x_2021_ = lean_st_ref_set(v___x_2016_, v___x_2020_);
if (lean_obj_tag(v___x_2017_) == 1)
{
lean_object* v_val_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v___x_2015_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v___x_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2008_);
lean_dec_ref(v___x_2007_);
v_val_2022_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2024_ = v___x_2017_;
v_isShared_2025_ = v_isSharedCheck_2031_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_val_2022_);
lean_dec(v___x_2017_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2031_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2026_ = lean_io_wait(v_val_2022_);
lean_dec(v___x_2026_);
v___x_2027_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_object* v_cancelTk_x3f_2032_; 
lean_dec(v___x_2017_);
v_cancelTk_x3f_2032_ = lean_ctor_get(v___y_2012_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2032_) == 1)
{
lean_object* v_val_2033_; lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_val_2033_ = lean_ctor_get(v_cancelTk_x3f_2032_, 0);
lean_inc(v_val_2033_);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_2034_, 0, v_val_2033_);
lean_closure_set(v___f_2034_, 1, v___x_2015_);
v___x_2035_ = lean_box(0);
v___x_2036_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0));
v___x_2037_ = l_Lean_Name_mkStr5(v___x_2007_, v___x_2008_, v___x_2009_, v___x_2010_, v___x_2036_);
v___x_2038_ = l_Lean_Name_toString(v___x_2037_, v___x_2011_);
lean_inc_ref(v___y_2012_);
v___x_2039_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_2034_, v___x_2035_, v___x_2038_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2039_);
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_apply_1(v_a_2040_, v___x_2041_);
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_io_as_task(v___x_2042_, v___x_2043_);
v___x_2045_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_2032_);
v___x_2046_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2035_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
lean_ctor_set(v___x_2046_, 2, v_cancelTk_x3f_2032_);
lean_ctor_set(v___x_2046_, 3, v___x_2044_);
v___x_2047_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2046_, v___y_2013_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref(v___x_2047_);
v___x_2048_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_2049_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_2048_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
return v___x_2049_;
}
else
{
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v___x_2047_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
v_a_2050_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2039_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2039_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v___x_2015_);
lean_dec_ref(v___x_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2008_);
lean_dec_ref(v___x_2007_);
v___x_2058_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2);
v___x_2059_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v___x_2058_, v___y_2012_, v___y_2013_);
return v___x_2059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed(lean_object* v___x_2062_, lean_object* v___x_2063_, lean_object* v___x_2064_, lean_object* v___x_2065_, lean_object* v___x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
uint8_t v___x_7819__boxed_2070_; lean_object* v_res_2071_; 
v___x_7819__boxed_2070_ = lean_unbox(v___x_2066_);
v_res_2071_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(v___x_2062_, v___x_2063_, v___x_2064_, v___x_2065_, v___x_7819__boxed_2070_, v___y_2067_, v___y_2068_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(lean_object* v_x_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2076_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_2077_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_2078_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_2079_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_2080_ = ((lean_object*)(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1));
v___x_2081_ = l_Lean_Syntax_isOfKind(v_x_2072_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
lean_dec_ref(v_a_2073_);
v___x_2082_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_box(v___x_2081_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2084_, 0, v___x_2076_);
lean_closure_set(v___f_2084_, 1, v___x_2077_);
lean_closure_set(v___f_2084_, 2, v___x_2078_);
lean_closure_set(v___f_2084_, 3, v___x_2079_);
lean_closure_set(v___f_2084_, 4, v___x_2083_);
v___x_2085_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_2084_, v_a_2073_, v_a_2074_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___boxed(lean_object* v_x_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(v_x_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(lean_object* v_val_2091_, lean_object* v_b_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_2091_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(lean_object* v_val_2097_, lean_object* v_b_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(v_val_2097_, v_b_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v_val_2097_);
return v_res_2102_;
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
res = l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_onceRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_onceRef);
lean_dec_ref(res);
res = l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2473215001____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_unblockedCancelTk = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_unblockedCancelTk);
lean_dec_ref(res);
res = l_Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
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
