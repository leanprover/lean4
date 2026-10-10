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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*);
lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
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
static const lean_closure_object l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0 = (const lean_object*)&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cancelled!"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "cancelled (should never be visible)"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value)}};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Server.Test.Cancel"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_cancel_once_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "blocked!"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_unblockedCancelTkRef;
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "_aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_unblock_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticWait_for_unblock_1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_testTasksRef;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_mkTestTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_mkTestTask___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "tacticWait_for_test_task_"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 241, 171, 98, 172, 75, 180, 122)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "wait_for_test_task "};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__test__task__ = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "wait_for_test_task: no task registered for "};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "wait_for_test_task: task "};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = " dropped without resolution"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_syncPromisesRef;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_getSyncPromise(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_getSyncPromise___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_resolveSyncPromise(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_resolveSyncPromise___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticWait_for_sync_"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 215, 46, 16, 187, 62, 147, 151)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "wait_for_sync "};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticWait__for__sync__ = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5_value;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "wait_for_sync: sync promise "};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticBlock_until_cancelled_"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 90, 51, 119, 206, 46, 163, 7)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value),LEAN_SCALAR_PTR_LITERAL(102, 99, 52, 168, 19, 159, 18, 198)}};
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 22, 208, 150, 242, 79, 233, 148)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value;
static const lean_string_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "block_until_cancelled"};
static const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3_value),((lean_object*)&l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4_value;
static const lean_ctor_object l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4_value)}};
static const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5 = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled__ = (const lean_object*)&l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 120, .m_capacity = 120, .m_length = 119, .m_data = "Lean.Server.Test.Cancel._aux_Lean_Server_Test_Cancel___elabRules_Lean_Server_Test_Cancel_tacticBlock_until_cancelled__1"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0_value;
static lean_once_cell_t l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1;
static const lean_string_object l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ": blocked"};
static const lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2 = (const lean_object*)&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5_;
v_res_5_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2____boxed(lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
return v_res_7_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_box(0);
v___x_29_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
return v___x_30_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg(){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_34_;
v_res_34_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___boxed(lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v_res_36_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(lean_object* v_00_u03b1_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_47_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_38_ = stack[1].m_obj;
lean_object* v___y_39_ = stack[2].m_obj;
lean_object* v___y_40_ = stack[3].m_obj;
lean_object* v___y_41_ = stack[4].m_obj;
lean_object* v___y_42_ = stack[5].m_obj;
lean_object* v___y_43_ = stack[6].m_obj;
lean_object* v___y_44_ = stack[7].m_obj;
lean_object* v___y_45_ = stack[8].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(lean_box(0), v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___boxed(lean_object* v_00_u03b1_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(v_00_u03b1_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = l_Lean_interruptExceptionId;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg(){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_66_;
v_res_66_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___boxed(lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v_res_68_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(lean_object* v_00_u03b1_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_70_ = stack[1].m_obj;
lean_object* v___y_71_ = stack[2].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(lean_box(0), v___y_70_, v___y_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___boxed(lean_object* v_00_u03b1_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(v_00_u03b1_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_79_;
}
}
lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(lean_object* v_msg_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_9710__overap_92_; lean_object* v___x_93_; 
v___f_91_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0));
v___x_9710__overap_92_ = lean_panic_fn_borrowed(v___f_91_, v_msg_81_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
v___x_93_ = lean_apply_9(v___x_9710__overap_92_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_81_ = stack[0].m_obj;
lean_object* v___y_82_ = stack[1].m_obj;
lean_object* v___y_83_ = stack[2].m_obj;
lean_object* v___y_84_ = stack[3].m_obj;
lean_object* v___y_85_ = stack[4].m_obj;
lean_object* v___y_86_ = stack[5].m_obj;
lean_object* v___y_87_ = stack[6].m_obj;
lean_object* v___y_88_ = stack[7].m_obj;
lean_object* v___y_89_ = stack[8].m_obj;
lean_object* v_res_94_;
v_res_94_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v_msg_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___boxed(lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_105_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(lean_object* v_val_106_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_box(0);
v___x_109_ = l_IO_CancelToken_isSet(v_val_106_);
if (v___x_109_ == 0)
{
uint32_t v___x_110_; lean_object* v___x_111_; 
v___x_110_ = 30;
v___x_111_ = l_IO_sleep(v___x_110_);
goto _start;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_108_);
return v___x_113_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_106_ = stack[0].m_obj;
lean_object* v_res_114_;
v_res_114_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_106_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg___boxed(lean_object* v_val_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_115_);
lean_dec_ref(v_val_115_);
return v_res_117_;
}
}
lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(lean_object* v_s_118_){
_start:
{
lean_object* v___x_120_; lean_object* v_putStr_121_; lean_object* v___x_122_; 
v___x_120_ = lean_get_stderr();
v_putStr_121_ = lean_ctor_get(v___x_120_, 4);
lean_inc_ref(v_putStr_121_);
lean_dec_ref(v___x_120_);
v___x_122_ = lean_apply_2(v_putStr_121_, v_s_118_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_118_ = stack[0].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v_s_118_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4___boxed(lean_object* v_s_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v_s_124_);
return v_res_126_;
}
}
lean_object* l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(lean_object* v_s_127_){
_start:
{
uint32_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = 10;
v___x_130_ = lean_string_push(v_s_127_, v___x_129_);
v___x_131_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_127_ = stack[0].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v_s_127_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3___boxed(lean_object* v_s_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v_s_133_);
return v_res_135_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(lean_object* v_msgData_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v_env_143_; uint8_t v___x_144_; lean_object* v_env_145_; lean_object* v___x_146_; lean_object* v_toCold_147_; lean_object* v_mctx_148_; lean_object* v_lctx_149_; lean_object* v_options_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_142_ = lean_st_ref_get(v___y_140_);
v_env_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc_ref(v_env_143_);
lean_dec(v___x_142_);
v___x_144_ = 0;
v_env_145_ = l_Lean_Environment_setRecordingDeps(v_env_143_, v___x_144_);
v___x_146_ = lean_st_ref_get(v___y_138_);
v_toCold_147_ = lean_ctor_get(v___y_139_, 0);
v_mctx_148_ = lean_ctor_get(v___x_146_, 0);
lean_inc_ref(v_mctx_148_);
lean_dec(v___x_146_);
v_lctx_149_ = lean_ctor_get(v___y_137_, 2);
v_options_150_ = lean_ctor_get(v_toCold_147_, 2);
lean_inc_ref(v_options_150_);
lean_inc_ref(v_lctx_149_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v_env_145_);
lean_ctor_set(v___x_151_, 1, v_mctx_148_);
lean_ctor_set(v___x_151_, 2, v_lctx_149_);
lean_ctor_set(v___x_151_, 3, v_options_150_);
v___x_152_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_msgData_136_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_136_ = stack[0].m_obj;
lean_object* v___y_137_ = stack[1].m_obj;
lean_object* v___y_138_ = stack[2].m_obj;
lean_object* v___y_139_ = stack[3].m_obj;
lean_object* v___y_140_ = stack[4].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v_msgData_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v_msgData_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(lean_object* v_opts_162_, lean_object* v_opt_163_){
_start:
{
lean_object* v_name_164_; lean_object* v_defValue_165_; lean_object* v_map_166_; lean_object* v___x_167_; 
v_name_164_ = lean_ctor_get(v_opt_163_, 0);
v_defValue_165_ = lean_ctor_get(v_opt_163_, 1);
v_map_166_ = lean_ctor_get(v_opts_162_, 0);
v___x_167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_166_, v_name_164_);
if (lean_obj_tag(v___x_167_) == 0)
{
uint8_t v___x_168_; 
v___x_168_ = lean_unbox(v_defValue_165_);
return v___x_168_;
}
else
{
lean_object* v_val_169_; 
v_val_169_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_167_, 1);
if (lean_obj_tag(v_val_169_) == 1)
{
uint8_t v_v_170_; 
v_v_170_ = lean_ctor_get_uint8(v_val_169_, 0);
lean_dec_ref_known(v_val_169_, 0);
return v_v_170_;
}
else
{
uint8_t v___x_171_; 
lean_dec(v_val_169_);
v___x_171_ = lean_unbox(v_defValue_165_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_162_ = stack[0].m_obj;
lean_object* v_opt_163_ = stack[1].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_opts_162_, v_opt_163_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5___boxed(lean_object* v_opts_173_, lean_object* v_opt_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_opts_173_, v_opt_174_);
lean_dec_ref(v_opt_174_);
lean_dec_ref(v_opts_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_185_, uint8_t v___y_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 1)
{
lean_object* v_pre_188_; 
v_pre_188_ = lean_ctor_get(v_x_187_, 0);
switch(lean_obj_tag(v_pre_188_))
{
case 1:
{
lean_object* v_pre_189_; 
v_pre_189_ = lean_ctor_get(v_pre_188_, 0);
switch(lean_obj_tag(v_pre_189_))
{
case 0:
{
lean_object* v_str_190_; lean_object* v_str_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_str_190_ = lean_ctor_get(v_x_187_, 1);
v_str_191_ = lean_ctor_get(v_pre_188_, 1);
v___x_192_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_193_ = lean_string_dec_eq(v_str_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_195_ = lean_string_dec_eq(v_str_191_, v___x_194_);
if (v___x_195_ == 0)
{
return v___x_195_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_197_ = lean_string_dec_eq(v_str_190_, v___x_196_);
if (v___x_197_ == 0)
{
return v___x_197_;
}
else
{
return v_suppressElabErrors_185_;
}
}
}
else
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_199_ = lean_string_dec_eq(v_str_190_, v___x_198_);
if (v___x_199_ == 0)
{
return v___x_199_;
}
else
{
return v_suppressElabErrors_185_;
}
}
}
case 1:
{
lean_object* v_pre_200_; 
v_pre_200_ = lean_ctor_get(v_pre_189_, 0);
if (lean_obj_tag(v_pre_200_) == 0)
{
lean_object* v_str_201_; lean_object* v_str_202_; lean_object* v_str_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_str_201_ = lean_ctor_get(v_x_187_, 1);
v_str_202_ = lean_ctor_get(v_pre_188_, 1);
v_str_203_ = lean_ctor_get(v_pre_189_, 1);
v___x_204_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_205_ = lean_string_dec_eq(v_str_203_, v___x_204_);
if (v___x_205_ == 0)
{
return v___x_205_;
}
else
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_207_ = lean_string_dec_eq(v_str_202_, v___x_206_);
if (v___x_207_ == 0)
{
return v___x_207_;
}
else
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_209_ = lean_string_dec_eq(v_str_201_, v___x_208_);
if (v___x_209_ == 0)
{
return v___x_209_;
}
else
{
return v_suppressElabErrors_185_;
}
}
}
}
else
{
return v___y_186_;
}
}
default: 
{
return v___y_186_;
}
}
}
case 0:
{
lean_object* v_str_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_str_210_ = lean_ctor_get(v_x_187_, 1);
v___x_211_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_212_ = lean_string_dec_eq(v_str_210_, v___x_211_);
if (v___x_212_ == 0)
{
return v___x_212_;
}
else
{
return v_suppressElabErrors_185_;
}
}
default: 
{
return v___y_186_;
}
}
}
else
{
return v___y_186_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_185_ = stack[0].m_num;
uint8_t v___y_186_ = stack[1].m_num;
lean_object* v_x_187_ = stack[2].m_obj;
uint8_t v_res_213_;
v_res_213_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(v_suppressElabErrors_185_, v___y_186_, v_x_187_);
stack->m_num = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_214_, lean_object* v___y_215_, lean_object* v_x_216_){
_start:
{
uint8_t v_suppressElabErrors_boxed_217_; uint8_t v___y_14422__boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_suppressElabErrors_boxed_217_ = lean_unbox(v_suppressElabErrors_214_);
v___y_14422__boxed_218_ = lean_unbox(v___y_215_);
v_res_219_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_217_, v___y_14422__boxed_218_, v_x_216_);
lean_dec(v_x_216_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(lean_object* v_ref_222_, lean_object* v_msgData_223_, uint8_t v_severity_224_, uint8_t v_isSilent_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___y_232_; uint8_t v___y_233_; uint8_t v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v_toCold_239_; lean_object* v___y_240_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; uint8_t v___y_274_; uint8_t v___y_275_; lean_object* v___y_276_; lean_object* v___y_296_; lean_object* v___y_297_; uint8_t v___y_298_; uint8_t v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; lean_object* v___y_302_; uint8_t v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; uint8_t v___x_319_; uint8_t v___y_321_; uint8_t v___y_322_; uint8_t v___y_323_; uint8_t v___y_325_; uint8_t v___x_333_; 
v___x_319_ = 2;
v___x_333_ = l_Lean_instBEqMessageSeverity_beq(v_severity_224_, v___x_319_);
if (v___x_333_ == 0)
{
v___y_325_ = v___x_333_;
goto v___jp_324_;
}
else
{
uint8_t v___x_334_; 
lean_inc_ref(v_msgData_223_);
v___x_334_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_223_);
v___y_325_ = v___x_334_;
goto v___jp_324_;
}
v___jp_231_:
{
lean_object* v_currNamespace_241_; lean_object* v_openDecls_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_env_247_; lean_object* v_nextMacroScope_248_; lean_object* v_ngen_249_; lean_object* v_auxDeclNGen_250_; lean_object* v_traceState_251_; lean_object* v_cache_252_; lean_object* v_recordedDeps_253_; lean_object* v_messages_254_; lean_object* v_infoState_255_; lean_object* v_snapshotTasks_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_267_; 
v_currNamespace_241_ = lean_ctor_get(v_toCold_239_, 4);
v_openDecls_242_ = lean_ctor_get(v_toCold_239_, 5);
lean_inc(v_openDecls_242_);
lean_inc(v_currNamespace_241_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_currNamespace_241_);
lean_ctor_set(v___x_243_, 1, v_openDecls_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_232_);
lean_inc_ref(v___y_236_);
lean_inc_ref(v___y_238_);
v___x_245_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_245_, 0, v___y_238_);
lean_ctor_set(v___x_245_, 1, v___y_235_);
lean_ctor_set(v___x_245_, 2, v___y_237_);
lean_ctor_set(v___x_245_, 3, v___y_236_);
lean_ctor_set(v___x_245_, 4, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5, v___y_234_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 1, v___y_233_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*5 + 2, v_isSilent_225_);
v___x_246_ = lean_st_ref_take(v___y_240_);
v_env_247_ = lean_ctor_get(v___x_246_, 0);
v_nextMacroScope_248_ = lean_ctor_get(v___x_246_, 1);
v_ngen_249_ = lean_ctor_get(v___x_246_, 2);
v_auxDeclNGen_250_ = lean_ctor_get(v___x_246_, 3);
v_traceState_251_ = lean_ctor_get(v___x_246_, 4);
v_cache_252_ = lean_ctor_get(v___x_246_, 5);
v_recordedDeps_253_ = lean_ctor_get(v___x_246_, 6);
v_messages_254_ = lean_ctor_get(v___x_246_, 7);
v_infoState_255_ = lean_ctor_get(v___x_246_, 8);
v_snapshotTasks_256_ = lean_ctor_get(v___x_246_, 9);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_267_ == 0)
{
v___x_258_ = v___x_246_;
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snapshotTasks_256_);
lean_inc(v_infoState_255_);
lean_inc(v_messages_254_);
lean_inc(v_recordedDeps_253_);
lean_inc(v_cache_252_);
lean_inc(v_traceState_251_);
lean_inc(v_auxDeclNGen_250_);
lean_inc(v_ngen_249_);
lean_inc(v_nextMacroScope_248_);
lean_inc(v_env_247_);
lean_dec(v___x_246_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_260_ = lean_box(0);
v___x_261_ = l_Lean_MessageLog_add(v___x_245_, v_messages_254_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 7, v___x_261_);
v___x_263_ = v___x_258_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_env_247_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_nextMacroScope_248_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_ngen_249_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_auxDeclNGen_250_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_traceState_251_);
lean_ctor_set(v_reuseFailAlloc_266_, 5, v_cache_252_);
lean_ctor_set(v_reuseFailAlloc_266_, 6, v_recordedDeps_253_);
lean_ctor_set(v_reuseFailAlloc_266_, 7, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_266_, 8, v_infoState_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 9, v_snapshotTasks_256_);
v___x_263_ = v_reuseFailAlloc_266_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_st_ref_put(v___y_240_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_260_);
return v___x_265_;
}
}
}
v___jp_268_:
{
lean_object* v_fileName_277_; lean_object* v_fileMap_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_294_; 
v_fileName_277_ = lean_ctor_get(v___y_273_, 0);
v_fileMap_278_ = lean_ctor_get(v___y_273_, 1);
v___x_279_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_223_);
v___x_280_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_279_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_294_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_294_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_294_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_inc_ref_n(v_fileMap_278_, 2);
v___x_285_ = l_Lean_FileMap_toPosition(v_fileMap_278_, v___y_271_);
lean_dec(v___y_271_);
v___x_286_ = l_Lean_FileMap_toPosition(v_fileMap_278_, v___y_276_);
lean_dec(v___y_276_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_274_ == 0)
{
lean_del_object(v___x_283_);
lean_dec_ref(v___y_270_);
v___y_232_ = v_a_281_;
v___y_233_ = v___y_272_;
v___y_234_ = v___y_275_;
v___y_235_ = v___x_285_;
v___y_236_ = v___x_288_;
v___y_237_ = v___x_287_;
v___y_238_ = v_fileName_277_;
v_toCold_239_ = v___y_269_;
v___y_240_ = v___y_229_;
goto v___jp_231_;
}
else
{
uint8_t v___x_289_; 
lean_inc(v_a_281_);
v___x_289_ = l_Lean_MessageData_hasTag(v___y_270_, v_a_281_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_dec_ref_known(v___x_287_, 1);
lean_dec_ref(v___x_285_);
lean_dec(v_a_281_);
v___x_290_ = lean_box(0);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_290_);
v___x_292_ = v___x_283_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_del_object(v___x_283_);
v___y_232_ = v_a_281_;
v___y_233_ = v___y_272_;
v___y_234_ = v___y_275_;
v___y_235_ = v___x_285_;
v___y_236_ = v___x_288_;
v___y_237_ = v___x_287_;
v___y_238_ = v_fileName_277_;
v_toCold_239_ = v___y_269_;
v___y_240_ = v___y_229_;
goto v___jp_231_;
}
}
}
}
v___jp_295_:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Syntax_getTailPos_x3f(v___y_300_, v___y_301_);
lean_dec(v___y_300_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_inc(v___y_302_);
v___y_269_ = v___y_296_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_302_;
v___y_272_ = v___y_299_;
v___y_273_ = v___y_296_;
v___y_274_ = v___y_298_;
v___y_275_ = v___y_301_;
v___y_276_ = v___y_302_;
goto v___jp_268_;
}
else
{
lean_object* v_val_304_; 
v_val_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v___x_303_, 1);
v___y_269_ = v___y_296_;
v___y_270_ = v___y_297_;
v___y_271_ = v___y_302_;
v___y_272_ = v___y_299_;
v___y_273_ = v___y_296_;
v___y_274_ = v___y_298_;
v___y_275_ = v___y_301_;
v___y_276_ = v_val_304_;
goto v___jp_268_;
}
}
v___jp_305_:
{
lean_object* v_toCold_309_; lean_object* v_ref_310_; uint8_t v_suppressElabErrors_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v_ref_315_; lean_object* v___x_316_; 
v_toCold_309_ = lean_ctor_get(v___y_228_, 0);
v_ref_310_ = lean_ctor_get(v___y_228_, 2);
v_suppressElabErrors_311_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*3 + 2);
v___x_312_ = lean_box(v_suppressElabErrors_311_);
v___x_313_ = lean_box(v___y_306_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_314_, 0, v___x_312_);
lean_closure_set(v___f_314_, 1, v___x_313_);
v_ref_315_ = l_Lean_replaceRef(v_ref_222_, v_ref_310_);
v___x_316_ = l_Lean_Syntax_getPos_x3f(v_ref_315_, v___y_307_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___y_296_ = v_toCold_309_;
v___y_297_ = v___f_314_;
v___y_298_ = v_suppressElabErrors_311_;
v___y_299_ = v___y_308_;
v___y_300_ = v_ref_315_;
v___y_301_ = v___y_307_;
v___y_302_ = v___x_317_;
goto v___jp_295_;
}
else
{
lean_object* v_val_318_; 
v_val_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___x_316_, 1);
v___y_296_ = v_toCold_309_;
v___y_297_ = v___f_314_;
v___y_298_ = v_suppressElabErrors_311_;
v___y_299_ = v___y_308_;
v___y_300_ = v_ref_315_;
v___y_301_ = v___y_307_;
v___y_302_ = v_val_318_;
goto v___jp_295_;
}
}
v___jp_320_:
{
if (v___y_323_ == 0)
{
v___y_306_ = v___y_321_;
v___y_307_ = v___y_322_;
v___y_308_ = v_severity_224_;
goto v___jp_305_;
}
else
{
v___y_306_ = v___y_321_;
v___y_307_ = v___y_322_;
v___y_308_ = v___x_319_;
goto v___jp_305_;
}
}
v___jp_324_:
{
if (v___y_325_ == 0)
{
uint8_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 1;
v___x_327_ = l_Lean_instBEqMessageSeverity_beq(v_severity_224_, v___x_326_);
if (v___x_327_ == 0)
{
v___y_321_ = v___y_325_;
v___y_322_ = v___y_325_;
v___y_323_ = v___x_327_;
goto v___jp_320_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_228_);
v___x_329_ = l_Lean_warningAsError;
v___x_330_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v___x_328_, v___x_329_);
lean_dec_ref(v___x_328_);
v___y_321_ = v___y_325_;
v___y_322_ = v___y_325_;
v___y_323_ = v___x_330_;
goto v___jp_320_;
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v_msgData_223_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_222_ = stack[0].m_obj;
lean_object* v_msgData_223_ = stack[1].m_obj;
uint8_t v_severity_224_ = stack[2].m_num;
uint8_t v_isSilent_225_ = stack[3].m_num;
lean_object* v___y_226_ = stack[4].m_obj;
lean_object* v___y_227_ = stack[5].m_obj;
lean_object* v___y_228_ = stack[6].m_obj;
lean_object* v___y_229_ = stack[7].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_222_, v_msgData_223_, v_severity_224_, v_isSilent_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_336_, lean_object* v_msgData_337_, lean_object* v_severity_338_, lean_object* v_isSilent_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
uint8_t v_severity_boxed_345_; uint8_t v_isSilent_boxed_346_; lean_object* v_res_347_; 
v_severity_boxed_345_ = lean_unbox(v_severity_338_);
v_isSilent_boxed_346_ = lean_unbox(v_isSilent_339_);
v_res_347_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_336_, v_msgData_337_, v_severity_boxed_345_, v_isSilent_boxed_346_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v_ref_336_);
return v_res_347_;
}
}
lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(lean_object* v_msgData_348_, uint8_t v_severity_349_, uint8_t v_isSilent_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_ref_360_; lean_object* v___x_361_; 
v_ref_360_ = lean_ctor_get(v___y_357_, 2);
v___x_361_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_360_, v_msgData_348_, v_severity_349_, v_isSilent_350_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_348_ = stack[0].m_obj;
uint8_t v_severity_349_ = stack[1].m_num;
uint8_t v_isSilent_350_ = stack[2].m_num;
lean_object* v___y_351_ = stack[3].m_obj;
lean_object* v___y_352_ = stack[4].m_obj;
lean_object* v___y_353_ = stack[5].m_obj;
lean_object* v___y_354_ = stack[6].m_obj;
lean_object* v___y_355_ = stack[7].m_obj;
lean_object* v___y_356_ = stack[8].m_obj;
lean_object* v___y_357_ = stack[9].m_obj;
lean_object* v___y_358_ = stack[10].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v_msgData_348_, v_severity_349_, v_isSilent_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1___boxed(lean_object* v_msgData_363_, lean_object* v_severity_364_, lean_object* v_isSilent_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
uint8_t v_severity_boxed_375_; uint8_t v_isSilent_boxed_376_; lean_object* v_res_377_; 
v_severity_boxed_375_ = lean_unbox(v_severity_364_);
v_isSilent_boxed_376_ = lean_unbox(v_isSilent_365_);
v_res_377_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v_msgData_363_, v_severity_boxed_375_, v_isSilent_boxed_376_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_377_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1));
v___x_382_ = l_Lean_MessageData_ofFormat(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_unsigned_to_nat(32u);
v___x_384_ = lean_mk_empty_array_with_capacity(v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7));
v___x_392_ = l_Lean_MessageData_ofFormat(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_397_ = lean_unsigned_to_nat(39u);
v___x_398_ = lean_unsigned_to_nat(52u);
v___x_399_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_400_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_401_ = l_mkPanicMessageWithDecl(v___x_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_403_ = lean_unsigned_to_nat(37u);
v___x_404_ = lean_unsigned_to_nat(44u);
v___x_405_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_406_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_407_ = l_mkPanicMessageWithDecl(v___x_406_, v___x_405_, v___x_404_, v___x_403_, v___x_402_);
return v___x_407_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, uint8_t v___x_413_, lean_object* v___x_414_, lean_object* v_val_415_, lean_object* v_x_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_427_ = 2;
v___x_428_ = 0;
v___x_429_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_426_, v___x_427_, v___x_428_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_tacSnap_x3f_430_; 
lean_dec_ref_known(v___x_429_, 1);
v_tacSnap_x3f_430_ = lean_ctor_get(v___y_419_, 6);
if (lean_obj_tag(v_tacSnap_x3f_430_) == 1)
{
lean_object* v_val_431_; lean_object* v___x_432_; 
v_val_431_ = lean_ctor_get(v_tacSnap_x3f_430_, 0);
v___x_432_ = l_Lean_Core_getMessageLog___redArg(v___y_424_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; size_t v___x_438_; lean_object* v___x_439_; lean_object* v_new_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint64_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_toCold_456_; lean_object* v_cancelTk_x3f_457_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_433_);
v___x_435_ = lean_unsigned_to_nat(32u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_435_);
v___x_437_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_438_ = ((size_t)5ULL);
lean_inc_n(v___x_408_, 2);
v___x_439_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_436_);
lean_ctor_set(v___x_439_, 2, v___x_408_);
lean_ctor_set(v___x_439_, 3, v___x_408_);
lean_ctor_set_usize(v___x_439_, 4, v___x_438_);
v_new_440_ = lean_ctor_get(v_val_431_, 1);
v___x_441_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4));
v___x_442_ = l_Lean_Name_mkStr5(v___x_409_, v___x_410_, v___x_411_, v___x_412_, v___x_441_);
v___x_443_ = l_Lean_Name_toString(v___x_442_, v___x_413_);
v___x_444_ = lean_box(0);
v___x_445_ = 0ULL;
v___x_446_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_446_, 0, v___x_439_);
lean_ctor_set_uint64(v___x_446_, sizeof(void*)*1, v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_447_, 0, v___x_443_);
lean_ctor_set(v___x_447_, 1, v___x_434_);
lean_ctor_set(v___x_447_, 2, v___x_444_);
lean_ctor_set(v___x_447_, 3, v___x_446_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*4, v___x_428_);
v___x_448_ = lean_box(0);
v___x_449_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_414_);
v___x_450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_447_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
lean_ctor_set(v___x_450_, 2, v___x_444_);
lean_ctor_set(v___x_450_, 3, v___x_449_);
v___x_451_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_mk_empty_array_with_capacity(v___x_408_);
lean_dec(v___x_408_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_io_promise_resolve(v___x_454_, v_new_440_);
v_toCold_456_ = lean_ctor_get(v___y_423_, 0);
v_cancelTk_x3f_457_ = lean_ctor_get(v_toCold_456_, 10);
if (lean_obj_tag(v_cancelTk_x3f_457_) == 1)
{
lean_object* v_ref_458_; lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_ref_458_ = lean_ctor_get(v___y_423_, 2);
v_val_459_ = lean_ctor_get(v_cancelTk_x3f_457_, 0);
v___x_460_ = lean_box(0);
v___x_461_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_494_; 
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_461_, 0);
lean_dec(v_unused_495_);
v___x_463_ = v___x_461_;
v_isShared_464_ = v_isSharedCheck_494_;
goto v_resetjp_462_;
}
else
{
lean_dec(v___x_461_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_494_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_466_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec_ref_known(v___x_466_, 1);
lean_del_object(v___x_463_);
v___x_467_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_468_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_467_, v___x_427_, v___x_428_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___x_468_, 0);
lean_dec(v_unused_479_);
v___x_470_ = v___x_468_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_dec(v___x_468_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_io_promise_resolve(v___x_460_, v_val_415_);
v___x_473_ = l_IO_CancelToken_isSet(v_val_459_);
if (v___x_473_ == 0)
{
lean_object* v___x_475_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_460_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_460_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v___x_477_; 
lean_del_object(v___x_470_);
v___x_477_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_477_;
}
}
}
else
{
return v___x_468_;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_493_; 
v_a_480_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_493_ == 0)
{
v___x_482_ = v___x_466_;
v_isShared_483_ = v_isSharedCheck_493_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_466_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_493_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_io_error_to_string(v_a_480_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 3);
lean_ctor_set(v___x_463_, 0, v___x_484_);
v___x_486_ = v___x_463_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_492_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = l_Lean_MessageData_ofFormat(v___x_486_);
lean_inc(v_ref_458_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v_ref_458_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_488_);
v___x_490_ = v___x_482_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
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
}
}
else
{
return v___x_461_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12);
v___x_497_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_496_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
return v___x_497_;
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___x_409_);
lean_dec(v___x_408_);
v_a_498_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_432_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_432_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___x_409_);
lean_dec(v___x_408_);
v___x_506_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13);
v___x_507_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_506_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___x_409_);
lean_dec(v___x_408_);
return v___x_429_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_408_ = stack[0].m_obj;
lean_object* v___x_409_ = stack[1].m_obj;
lean_object* v___x_410_ = stack[2].m_obj;
lean_object* v___x_411_ = stack[3].m_obj;
lean_object* v___x_412_ = stack[4].m_obj;
uint8_t v___x_413_ = stack[5].m_num;
lean_object* v___x_414_ = stack[6].m_obj;
lean_object* v_val_415_ = stack[7].m_obj;
lean_object* v_x_416_ = stack[8].m_obj;
lean_object* v___y_417_ = stack[9].m_obj;
lean_object* v___y_418_ = stack[10].m_obj;
lean_object* v___y_419_ = stack[11].m_obj;
lean_object* v___y_420_ = stack[12].m_obj;
lean_object* v___y_421_ = stack[13].m_obj;
lean_object* v___y_422_ = stack[14].m_obj;
lean_object* v___y_423_ = stack[15].m_obj;
lean_object* v___y_424_ = stack[16].m_obj;
lean_object* v_res_508_;
v_res_508_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(v___x_408_, v___x_409_, v___x_410_, v___x_411_, v___x_412_, v___x_413_, v___x_414_, v_val_415_, v_x_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_509_ = _args[0];
lean_object* v___x_510_ = _args[1];
lean_object* v___x_511_ = _args[2];
lean_object* v___x_512_ = _args[3];
lean_object* v___x_513_ = _args[4];
lean_object* v___x_514_ = _args[5];
lean_object* v___x_515_ = _args[6];
lean_object* v_val_516_ = _args[7];
lean_object* v_x_517_ = _args[8];
lean_object* v___y_518_ = _args[9];
lean_object* v___y_519_ = _args[10];
lean_object* v___y_520_ = _args[11];
lean_object* v___y_521_ = _args[12];
lean_object* v___y_522_ = _args[13];
lean_object* v___y_523_ = _args[14];
lean_object* v___y_524_ = _args[15];
lean_object* v___y_525_ = _args[16];
lean_object* v___y_526_ = _args[17];
_start:
{
uint8_t v___x_14931__boxed_527_; lean_object* v_res_528_; 
v___x_14931__boxed_527_ = lean_unbox(v___x_514_);
v_res_528_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(v___x_509_, v___x_510_, v___x_511_, v___x_512_, v___x_513_, v___x_14931__boxed_527_, v___x_515_, v_val_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v_val_516_);
return v_res_528_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(lean_object* v_x_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_540_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_541_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_542_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_543_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_544_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5));
v___x_545_ = l_Lean_Syntax_isOfKind(v_x_530_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___y_555_; 
v___x_547_ = l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_io_promise_new();
v___x_550_ = lean_box(v___x_545_);
lean_inc(v___x_549_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed), 18, 8);
lean_closure_set(v___f_551_, 0, v___x_548_);
lean_closure_set(v___f_551_, 1, v___x_540_);
lean_closure_set(v___f_551_, 2, v___x_541_);
lean_closure_set(v___f_551_, 3, v___x_542_);
lean_closure_set(v___f_551_, 4, v___x_543_);
lean_closure_set(v___f_551_, 5, v___x_550_);
lean_closure_set(v___f_551_, 6, v___x_547_);
lean_closure_set(v___f_551_, 7, v___x_549_);
v___x_552_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_553_ = lean_st_ref_take(v___x_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_571_; 
v___x_571_ = l_IO_Promise_result_x21___redArg(v___x_549_);
lean_dec(v___x_549_);
v___y_555_ = v___x_571_;
goto v___jp_554_;
}
else
{
lean_object* v_val_572_; 
lean_dec(v___x_549_);
v_val_572_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_572_);
v___y_555_ = v_val_572_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___y_555_);
v___x_557_ = lean_st_ref_put(v___x_552_, v___x_556_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v___f_551_);
v_val_558_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_567_ == 0)
{
v___x_560_ = v___x_553_;
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v___x_553_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_567_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = lean_io_wait(v_val_558_);
lean_dec(v___x_562_);
v___x_563_ = lean_box(0);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 0);
lean_ctor_set(v___x_560_, 0, v___x_563_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_8807__overap_569_; lean_object* v___x_570_; 
lean_dec(v___x_553_);
v___x_568_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_8807__overap_569_ = lean_dbg_trace(v___x_568_, v___f_551_);
lean_inc(v_a_538_);
lean_inc_ref(v_a_537_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
v___x_570_ = lean_apply_9(v___x_8807__overap_569_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, lean_box(0));
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_530_ = stack[0].m_obj;
lean_object* v_a_531_ = stack[1].m_obj;
lean_object* v_a_532_ = stack[2].m_obj;
lean_object* v_a_533_ = stack[3].m_obj;
lean_object* v_a_534_ = stack[4].m_obj;
lean_object* v_a_535_ = stack[5].m_obj;
lean_object* v_a_536_ = stack[6].m_obj;
lean_object* v_a_537_ = stack[7].m_obj;
lean_object* v_a_538_ = stack[8].m_obj;
lean_object* v_res_573_;
v_res_573_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(v_x_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(lean_object* v_x_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(v_x_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_584_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(lean_object* v_val_585_, lean_object* v_inst_586_, lean_object* v_a_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_585_);
return v___x_597_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_585_ = stack[0].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v___y_588_ = stack[3].m_obj;
lean_object* v___y_589_ = stack[4].m_obj;
lean_object* v___y_590_ = stack[5].m_obj;
lean_object* v___y_591_ = stack[6].m_obj;
lean_object* v___y_592_ = stack[7].m_obj;
lean_object* v___y_593_ = stack[8].m_obj;
lean_object* v___y_594_ = stack[9].m_obj;
lean_object* v___y_595_ = stack[10].m_obj;
lean_object* v_res_598_;
v_res_598_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(v_val_585_, lean_box(0), v_a_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(lean_object* v_val_599_, lean_object* v_inst_600_, lean_object* v_a_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(v_val_599_, v_inst_600_, v_a_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec_ref(v_val_599_);
return v_res_611_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(lean_object* v_ref_612_, lean_object* v_msgData_613_, uint8_t v_severity_614_, uint8_t v_isSilent_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_612_, v_msgData_613_, v_severity_614_, v_isSilent_615_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
return v___x_625_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_612_ = stack[0].m_obj;
lean_object* v_msgData_613_ = stack[1].m_obj;
uint8_t v_severity_614_ = stack[2].m_num;
uint8_t v_isSilent_615_ = stack[3].m_num;
lean_object* v___y_616_ = stack[4].m_obj;
lean_object* v___y_617_ = stack[5].m_obj;
lean_object* v___y_618_ = stack[6].m_obj;
lean_object* v___y_619_ = stack[7].m_obj;
lean_object* v___y_620_ = stack[8].m_obj;
lean_object* v___y_621_ = stack[9].m_obj;
lean_object* v___y_622_ = stack[10].m_obj;
lean_object* v___y_623_ = stack[11].m_obj;
lean_object* v_res_626_;
v_res_626_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(v_ref_612_, v_msgData_613_, v_severity_614_, v_isSilent_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
stack->m_obj
 = v_res_626_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(lean_object* v_ref_627_, lean_object* v_msgData_628_, lean_object* v_severity_629_, lean_object* v_isSilent_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
uint8_t v_severity_boxed_640_; uint8_t v_isSilent_boxed_641_; lean_object* v_res_642_; 
v_severity_boxed_640_ = lean_unbox(v_severity_629_);
v_isSilent_boxed_641_ = lean_unbox(v_isSilent_630_);
v_res_642_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(v_ref_627_, v_msgData_628_, v_severity_boxed_640_, v_isSilent_boxed_641_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v_ref_627_);
return v_res_642_;
}
}
lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_box(0);
v___x_645_ = lean_st_mk_ref(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_647_;
v_res_647_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2____boxed(lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
return v_res_649_;
}
}
lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk(){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_fst_655_; lean_object* v_snd_656_; 
v___x_651_ = l_IO_CancelToken_new();
v___x_652_ = l_Lean_Server_Test_Cancel_unblockedCancelTkRef;
v___x_653_ = lean_st_ref_take(v___x_652_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_658_; 
lean_inc_ref(v___x_651_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_651_);
v_fst_655_ = v___x_651_;
v_snd_656_ = v___x_658_;
goto v___jp_654_;
}
else
{
lean_object* v_val_659_; 
lean_dec_ref(v___x_651_);
v_val_659_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_659_);
v_fst_655_ = v_val_659_;
v_snd_656_ = v___x_653_;
goto v___jp_654_;
}
v___jp_654_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_st_ref_put(v___x_652_, v_snd_656_);
return v_fst_655_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_660_;
v_res_660_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk___boxed(lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
return v_res_662_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg(){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_box(0);
v___x_681_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
v___x_682_ = l_IO_CancelToken_isSet(v___x_681_);
lean_dec_ref(v___x_681_);
if (v___x_682_ == 0)
{
uint32_t v___x_683_; lean_object* v___x_684_; 
v___x_683_ = 30;
v___x_684_ = l_IO_sleep(v___x_683_);
goto _start;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_680_);
return v___x_686_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_687_;
v_res_687_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v_res_689_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_692_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_693_ = lean_unsigned_to_nat(37u);
v___x_694_ = lean_unsigned_to_nat(89u);
v___x_695_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_696_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_697_ = l_mkPanicMessageWithDecl(v___x_696_, v___x_695_, v___x_694_, v___x_693_, v___x_692_);
return v___x_697_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v___x_702_, uint8_t v___x_703_, lean_object* v___x_704_, lean_object* v_val_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_717_ = 2;
v___x_718_ = 0;
v___x_719_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_716_, v___x_717_, v___x_718_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_789_; 
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_790_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_789_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_789_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_tacSnap_x3f_723_; 
v_tacSnap_x3f_723_ = lean_ctor_get(v___y_709_, 6);
if (lean_obj_tag(v_tacSnap_x3f_723_) == 1)
{
lean_object* v_val_724_; lean_object* v___x_725_; 
v_val_724_ = lean_ctor_get(v_tacSnap_x3f_723_, 0);
v___x_725_ = l_Lean_Core_getMessageLog___redArg(v___y_714_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; size_t v___x_731_; lean_object* v___x_732_; lean_object* v_new_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint64_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_726_);
v___x_728_ = lean_unsigned_to_nat(32u);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_731_ = ((size_t)5ULL);
lean_inc_n(v___x_698_, 2);
v___x_732_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_729_);
lean_ctor_set(v___x_732_, 2, v___x_698_);
lean_ctor_set(v___x_732_, 3, v___x_698_);
lean_ctor_set_usize(v___x_732_, 4, v___x_731_);
v_new_733_ = lean_ctor_get(v_val_724_, 1);
v___x_734_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0));
v___x_735_ = l_Lean_Name_mkStr5(v___x_699_, v___x_700_, v___x_701_, v___x_702_, v___x_734_);
v___x_736_ = l_Lean_Name_toString(v___x_735_, v___x_703_);
v___x_737_ = lean_box(0);
v___x_738_ = 0ULL;
v___x_739_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_739_, 0, v___x_732_);
lean_ctor_set_uint64(v___x_739_, sizeof(void*)*1, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_740_, 0, v___x_736_);
lean_ctor_set(v___x_740_, 1, v___x_727_);
lean_ctor_set(v___x_740_, 2, v___x_737_);
lean_ctor_set(v___x_740_, 3, v___x_739_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*4, v___x_718_);
v___x_741_ = lean_box(0);
v___x_742_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_704_);
v___x_743_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_743_, 0, v___x_740_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
lean_ctor_set(v___x_743_, 2, v___x_737_);
lean_ctor_set(v___x_743_, 3, v___x_742_);
v___x_744_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_698_);
lean_dec(v___x_698_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_io_promise_resolve(v___x_747_, v_new_733_);
v___x_749_ = lean_box(0);
v___x_750_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_777_; 
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_778_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_777_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_777_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; 
v___x_754_ = l_IO_CancelToken_isSet(v_val_705_);
if (v___x_754_ == 0)
{
lean_object* v___x_756_; 
lean_del_object(v___x_721_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_749_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_749_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v_ref_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_del_object(v___x_752_);
v_ref_758_ = lean_ctor_get(v___y_713_, 2);
v___x_759_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_760_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref_known(v___x_760_, 1);
lean_del_object(v___x_721_);
v___x_761_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_762_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_761_, v___x_717_, v___x_718_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_762_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_776_; 
v_a_763_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_776_ == 0)
{
v___x_765_ = v___x_760_;
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = lean_io_error_to_string(v_a_763_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 3);
lean_ctor_set(v___x_721_, 0, v___x_767_);
v___x_769_ = v___x_721_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_775_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = l_Lean_MessageData_ofFormat(v___x_769_);
lean_inc(v_ref_758_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_ref_758_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_771_);
v___x_773_ = v___x_765_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_721_);
return v___x_750_;
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_del_object(v___x_721_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_700_);
lean_dec_ref(v___x_699_);
lean_dec(v___x_698_);
v_a_779_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_725_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_725_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_del_object(v___x_721_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_700_);
lean_dec_ref(v___x_699_);
lean_dec(v___x_698_);
v___x_787_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2);
v___x_788_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_787_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_788_;
}
}
}
else
{
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_702_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_700_);
lean_dec_ref(v___x_699_);
lean_dec(v___x_698_);
return v___x_719_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_698_ = stack[0].m_obj;
lean_object* v___x_699_ = stack[1].m_obj;
lean_object* v___x_700_ = stack[2].m_obj;
lean_object* v___x_701_ = stack[3].m_obj;
lean_object* v___x_702_ = stack[4].m_obj;
uint8_t v___x_703_ = stack[5].m_num;
lean_object* v___x_704_ = stack[6].m_obj;
lean_object* v_val_705_ = stack[7].m_obj;
lean_object* v_x_706_ = stack[8].m_obj;
lean_object* v___y_707_ = stack[9].m_obj;
lean_object* v___y_708_ = stack[10].m_obj;
lean_object* v___y_709_ = stack[11].m_obj;
lean_object* v___y_710_ = stack[12].m_obj;
lean_object* v___y_711_ = stack[13].m_obj;
lean_object* v___y_712_ = stack[14].m_obj;
lean_object* v___y_713_ = stack[15].m_obj;
lean_object* v___y_714_ = stack[16].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(v___x_698_, v___x_699_, v___x_700_, v___x_701_, v___x_702_, v___x_703_, v___x_704_, v_val_705_, v_x_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_792_ = _args[0];
lean_object* v___x_793_ = _args[1];
lean_object* v___x_794_ = _args[2];
lean_object* v___x_795_ = _args[3];
lean_object* v___x_796_ = _args[4];
lean_object* v___x_797_ = _args[5];
lean_object* v___x_798_ = _args[6];
lean_object* v_val_799_ = _args[7];
lean_object* v_x_800_ = _args[8];
lean_object* v___y_801_ = _args[9];
lean_object* v___y_802_ = _args[10];
lean_object* v___y_803_ = _args[11];
lean_object* v___y_804_ = _args[12];
lean_object* v___y_805_ = _args[13];
lean_object* v___y_806_ = _args[14];
lean_object* v___y_807_ = _args[15];
lean_object* v___y_808_ = _args[16];
lean_object* v___y_809_ = _args[17];
_start:
{
uint8_t v___x_6318__boxed_810_; lean_object* v_res_811_; 
v___x_6318__boxed_810_ = lean_unbox(v___x_797_);
v_res_811_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(v___x_792_, v___x_793_, v___x_794_, v___x_795_, v___x_796_, v___x_6318__boxed_810_, v___x_798_, v_val_799_, v_x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_val_799_);
return v_res_811_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_812_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_813_ = lean_unsigned_to_nat(39u);
v___x_814_ = lean_unsigned_to_nat(84u);
v___x_815_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_816_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_817_ = l_mkPanicMessageWithDecl(v___x_816_, v___x_815_, v___x_814_, v___x_813_, v___x_812_);
return v___x_817_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(lean_object* v_x_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_828_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_829_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_830_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_831_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_832_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1));
v___x_833_ = l_Lean_Syntax_isOfKind(v_x_818_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_834_;
}
else
{
lean_object* v_toCold_835_; lean_object* v_cancelTk_x3f_836_; 
v_toCold_835_ = lean_ctor_get(v_a_825_, 0);
v_cancelTk_x3f_836_ = lean_ctor_get(v_toCold_835_, 10);
if (lean_obj_tag(v_cancelTk_x3f_836_) == 1)
{
lean_object* v_val_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_5778__overap_843_; lean_object* v___x_844_; 
v_val_837_ = lean_ctor_get(v_cancelTk_x3f_836_, 0);
v___x_838_ = l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_box(v___x_833_);
lean_inc(v_val_837_);
v___f_841_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed), 18, 8);
lean_closure_set(v___f_841_, 0, v___x_839_);
lean_closure_set(v___f_841_, 1, v___x_828_);
lean_closure_set(v___f_841_, 2, v___x_829_);
lean_closure_set(v___f_841_, 3, v___x_830_);
lean_closure_set(v___f_841_, 4, v___x_831_);
lean_closure_set(v___f_841_, 5, v___x_840_);
lean_closure_set(v___f_841_, 6, v___x_838_);
lean_closure_set(v___f_841_, 7, v_val_837_);
v___x_842_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_5778__overap_843_ = lean_dbg_trace(v___x_842_, v___f_841_);
lean_inc(v_a_826_);
lean_inc_ref(v_a_825_);
lean_inc(v_a_824_);
lean_inc_ref(v_a_823_);
lean_inc(v_a_822_);
lean_inc_ref(v_a_821_);
lean_inc(v_a_820_);
lean_inc_ref(v_a_819_);
v___x_844_ = lean_apply_9(v___x_5778__overap_843_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, lean_box(0));
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0);
v___x_846_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_845_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_846_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_818_ = stack[0].m_obj;
lean_object* v_a_819_ = stack[1].m_obj;
lean_object* v_a_820_ = stack[2].m_obj;
lean_object* v_a_821_ = stack[3].m_obj;
lean_object* v_a_822_ = stack[4].m_obj;
lean_object* v_a_823_ = stack[5].m_obj;
lean_object* v_a_824_ = stack[6].m_obj;
lean_object* v_a_825_ = stack[7].m_obj;
lean_object* v_a_826_ = stack[8].m_obj;
lean_object* v_res_847_;
v_res_847_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(v_x_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(lean_object* v_x_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(v_x_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_858_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_object* v_inst_859_, lean_object* v_a_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v___x_870_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_860_ = stack[1].m_obj;
lean_object* v___y_861_ = stack[2].m_obj;
lean_object* v___y_862_ = stack[3].m_obj;
lean_object* v___y_863_ = stack[4].m_obj;
lean_object* v___y_864_ = stack[5].m_obj;
lean_object* v___y_865_ = stack[6].m_obj;
lean_object* v___y_866_ = stack[7].m_obj;
lean_object* v___y_867_ = stack[8].m_obj;
lean_object* v___y_868_ = stack[9].m_obj;
lean_object* v_res_871_;
v_res_871_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_box(0), v_a_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(lean_object* v_inst_872_, lean_object* v_a_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(v_inst_872_, v_a_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_883_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_900_;
}
}
lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_4705__overap_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0, &l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0);
v___x_4705__overap_910_ = lean_panic_fn_borrowed(v___x_909_, v_msg_901_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
v___x_911_ = lean_apply_7(v___x_4705__overap_910_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
return v___x_911_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_901_ = stack[0].m_obj;
lean_object* v___y_902_ = stack[1].m_obj;
lean_object* v___y_903_ = stack[2].m_obj;
lean_object* v___y_904_ = stack[3].m_obj;
lean_object* v___y_905_ = stack[4].m_obj;
lean_object* v___y_906_ = stack[5].m_obj;
lean_object* v___y_907_ = stack[6].m_obj;
lean_object* v_res_912_;
v_res_912_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
stack->m_obj
 = v_res_912_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___boxed(lean_object* v_msg_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v_msg_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_921_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(lean_object* v_ref_922_, lean_object* v_msgData_923_, uint8_t v_severity_924_, uint8_t v_isSilent_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; uint8_t v___y_936_; uint8_t v___y_937_; lean_object* v___y_938_; lean_object* v_toCold_939_; lean_object* v___y_940_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; uint8_t v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_996_; uint8_t v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___y_1000_; uint8_t v___y_1001_; lean_object* v___y_1002_; uint8_t v___y_1006_; uint8_t v___y_1007_; uint8_t v___y_1008_; uint8_t v___x_1019_; uint8_t v___y_1021_; uint8_t v___y_1022_; uint8_t v___y_1023_; uint8_t v___y_1025_; uint8_t v___x_1033_; 
v___x_1019_ = 2;
v___x_1033_ = l_Lean_instBEqMessageSeverity_beq(v_severity_924_, v___x_1019_);
if (v___x_1033_ == 0)
{
v___y_1025_ = v___x_1033_;
goto v___jp_1024_;
}
else
{
uint8_t v___x_1034_; 
lean_inc_ref(v_msgData_923_);
v___x_1034_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_923_);
v___y_1025_ = v___x_1034_;
goto v___jp_1024_;
}
v___jp_931_:
{
lean_object* v_currNamespace_941_; lean_object* v_openDecls_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_env_947_; lean_object* v_nextMacroScope_948_; lean_object* v_ngen_949_; lean_object* v_auxDeclNGen_950_; lean_object* v_traceState_951_; lean_object* v_cache_952_; lean_object* v_recordedDeps_953_; lean_object* v_messages_954_; lean_object* v_infoState_955_; lean_object* v_snapshotTasks_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_967_; 
v_currNamespace_941_ = lean_ctor_get(v_toCold_939_, 4);
v_openDecls_942_ = lean_ctor_get(v_toCold_939_, 5);
lean_inc(v_openDecls_942_);
lean_inc(v_currNamespace_941_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_currNamespace_941_);
lean_ctor_set(v___x_943_, 1, v_openDecls_942_);
v___x_944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___y_933_);
lean_inc_ref(v___y_935_);
lean_inc_ref(v___y_938_);
v___x_945_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_945_, 0, v___y_938_);
lean_ctor_set(v___x_945_, 1, v___y_934_);
lean_ctor_set(v___x_945_, 2, v___y_932_);
lean_ctor_set(v___x_945_, 3, v___y_935_);
lean_ctor_set(v___x_945_, 4, v___x_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*5, v___y_937_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*5 + 1, v___y_936_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*5 + 2, v_isSilent_925_);
v___x_946_ = lean_st_ref_take(v___y_940_);
v_env_947_ = lean_ctor_get(v___x_946_, 0);
v_nextMacroScope_948_ = lean_ctor_get(v___x_946_, 1);
v_ngen_949_ = lean_ctor_get(v___x_946_, 2);
v_auxDeclNGen_950_ = lean_ctor_get(v___x_946_, 3);
v_traceState_951_ = lean_ctor_get(v___x_946_, 4);
v_cache_952_ = lean_ctor_get(v___x_946_, 5);
v_recordedDeps_953_ = lean_ctor_get(v___x_946_, 6);
v_messages_954_ = lean_ctor_get(v___x_946_, 7);
v_infoState_955_ = lean_ctor_get(v___x_946_, 8);
v_snapshotTasks_956_ = lean_ctor_get(v___x_946_, 9);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_967_ == 0)
{
v___x_958_ = v___x_946_;
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_snapshotTasks_956_);
lean_inc(v_infoState_955_);
lean_inc(v_messages_954_);
lean_inc(v_recordedDeps_953_);
lean_inc(v_cache_952_);
lean_inc(v_traceState_951_);
lean_inc(v_auxDeclNGen_950_);
lean_inc(v_ngen_949_);
lean_inc(v_nextMacroScope_948_);
lean_inc(v_env_947_);
lean_dec(v___x_946_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = lean_box(0);
v___x_961_ = l_Lean_MessageLog_add(v___x_945_, v_messages_954_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 7, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_env_947_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_nextMacroScope_948_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_ngen_949_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_auxDeclNGen_950_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_traceState_951_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_cache_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 6, v_recordedDeps_953_);
lean_ctor_set(v_reuseFailAlloc_966_, 7, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_966_, 8, v_infoState_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 9, v_snapshotTasks_956_);
v___x_963_ = v_reuseFailAlloc_966_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_st_ref_put(v___y_940_, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_960_);
return v___x_965_;
}
}
}
v___jp_968_:
{
lean_object* v_fileName_977_; lean_object* v_fileMap_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_994_; 
v_fileName_977_ = lean_ctor_get(v___y_973_, 0);
v_fileMap_978_ = lean_ctor_get(v___y_973_, 1);
v___x_979_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_923_);
v___x_980_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_979_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_994_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_994_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_994_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_inc_ref_n(v_fileMap_978_, 2);
v___x_985_ = l_Lean_FileMap_toPosition(v_fileMap_978_, v___y_971_);
lean_dec(v___y_971_);
v___x_986_ = l_Lean_FileMap_toPosition(v_fileMap_978_, v___y_976_);
lean_dec(v___y_976_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_972_ == 0)
{
lean_del_object(v___x_983_);
lean_dec_ref(v___y_969_);
v___y_932_ = v___x_987_;
v___y_933_ = v_a_981_;
v___y_934_ = v___x_985_;
v___y_935_ = v___x_988_;
v___y_936_ = v___y_974_;
v___y_937_ = v___y_975_;
v___y_938_ = v_fileName_977_;
v_toCold_939_ = v___y_970_;
v___y_940_ = v___y_929_;
goto v___jp_931_;
}
else
{
uint8_t v___x_989_; 
lean_inc(v_a_981_);
v___x_989_ = l_Lean_MessageData_hasTag(v___y_969_, v_a_981_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_992_; 
lean_dec_ref_known(v___x_987_, 1);
lean_dec_ref(v___x_985_);
lean_dec(v_a_981_);
v___x_990_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_990_);
v___x_992_ = v___x_983_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
lean_del_object(v___x_983_);
v___y_932_ = v___x_987_;
v___y_933_ = v_a_981_;
v___y_934_ = v___x_985_;
v___y_935_ = v___x_988_;
v___y_936_ = v___y_974_;
v___y_937_ = v___y_975_;
v___y_938_ = v_fileName_977_;
v_toCold_939_ = v___y_970_;
v___y_940_ = v___y_929_;
goto v___jp_931_;
}
}
}
}
v___jp_995_:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Syntax_getTailPos_x3f(v___y_999_, v___y_1001_);
lean_dec(v___y_999_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_inc(v___y_1002_);
v___y_969_ = v___y_996_;
v___y_970_ = v___y_998_;
v___y_971_ = v___y_1002_;
v___y_972_ = v___y_997_;
v___y_973_ = v___y_998_;
v___y_974_ = v___y_1000_;
v___y_975_ = v___y_1001_;
v___y_976_ = v___y_1002_;
goto v___jp_968_;
}
else
{
lean_object* v_val_1004_; 
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___y_969_ = v___y_996_;
v___y_970_ = v___y_998_;
v___y_971_ = v___y_1002_;
v___y_972_ = v___y_997_;
v___y_973_ = v___y_998_;
v___y_974_ = v___y_1000_;
v___y_975_ = v___y_1001_;
v___y_976_ = v_val_1004_;
goto v___jp_968_;
}
}
v___jp_1005_:
{
lean_object* v_toCold_1009_; lean_object* v_ref_1010_; uint8_t v_suppressElabErrors_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v_ref_1015_; lean_object* v___x_1016_; 
v_toCold_1009_ = lean_ctor_get(v___y_928_, 0);
v_ref_1010_ = lean_ctor_get(v___y_928_, 2);
v_suppressElabErrors_1011_ = lean_ctor_get_uint8(v___y_928_, sizeof(void*)*3 + 2);
v___x_1012_ = lean_box(v_suppressElabErrors_1011_);
v___x_1013_ = lean_box(v___y_1006_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1014_, 0, v___x_1012_);
lean_closure_set(v___f_1014_, 1, v___x_1013_);
v_ref_1015_ = l_Lean_replaceRef(v_ref_922_, v_ref_1010_);
v___x_1016_ = l_Lean_Syntax_getPos_x3f(v_ref_1015_, v___y_1007_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___y_996_ = v___f_1014_;
v___y_997_ = v_suppressElabErrors_1011_;
v___y_998_ = v_toCold_1009_;
v___y_999_ = v_ref_1015_;
v___y_1000_ = v___y_1008_;
v___y_1001_ = v___y_1007_;
v___y_1002_ = v___x_1017_;
goto v___jp_995_;
}
else
{
lean_object* v_val_1018_; 
v_val_1018_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v___x_1016_, 1);
v___y_996_ = v___f_1014_;
v___y_997_ = v_suppressElabErrors_1011_;
v___y_998_ = v_toCold_1009_;
v___y_999_ = v_ref_1015_;
v___y_1000_ = v___y_1008_;
v___y_1001_ = v___y_1007_;
v___y_1002_ = v_val_1018_;
goto v___jp_995_;
}
}
v___jp_1020_:
{
if (v___y_1023_ == 0)
{
v___y_1006_ = v___y_1021_;
v___y_1007_ = v___y_1022_;
v___y_1008_ = v_severity_924_;
goto v___jp_1005_;
}
else
{
v___y_1006_ = v___y_1021_;
v___y_1007_ = v___y_1022_;
v___y_1008_ = v___x_1019_;
goto v___jp_1005_;
}
}
v___jp_1024_:
{
if (v___y_1025_ == 0)
{
uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = 1;
v___x_1027_ = l_Lean_instBEqMessageSeverity_beq(v_severity_924_, v___x_1026_);
if (v___x_1027_ == 0)
{
v___y_1021_ = v___y_1025_;
v___y_1022_ = v___y_1025_;
v___y_1023_ = v___x_1027_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_928_);
v___x_1029_ = l_Lean_warningAsError;
v___x_1030_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v___x_1028_, v___x_1029_);
lean_dec_ref(v___x_1028_);
v___y_1021_ = v___y_1025_;
v___y_1022_ = v___y_1025_;
v___y_1023_ = v___x_1030_;
goto v___jp_1020_;
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_msgData_923_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_922_ = stack[0].m_obj;
lean_object* v_msgData_923_ = stack[1].m_obj;
uint8_t v_severity_924_ = stack[2].m_num;
uint8_t v_isSilent_925_ = stack[3].m_num;
lean_object* v___y_926_ = stack[4].m_obj;
lean_object* v___y_927_ = stack[5].m_obj;
lean_object* v___y_928_ = stack[6].m_obj;
lean_object* v___y_929_ = stack[7].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_922_, v_msgData_923_, v_severity_924_, v_isSilent_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_1036_, lean_object* v_msgData_1037_, lean_object* v_severity_1038_, lean_object* v_isSilent_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v_severity_boxed_1045_; uint8_t v_isSilent_boxed_1046_; lean_object* v_res_1047_; 
v_severity_boxed_1045_ = lean_unbox(v_severity_1038_);
v_isSilent_boxed_1046_ = lean_unbox(v_isSilent_1039_);
v_res_1047_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1036_, v_msgData_1037_, v_severity_boxed_1045_, v_isSilent_boxed_1046_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v_ref_1036_);
return v_res_1047_;
}
}
lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(lean_object* v_msgData_1048_, uint8_t v_severity_1049_, uint8_t v_isSilent_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_ref_1058_; lean_object* v___x_1059_; 
v_ref_1058_ = lean_ctor_get(v___y_1055_, 2);
v___x_1059_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1058_, v_msgData_1048_, v_severity_1049_, v_isSilent_1050_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1048_ = stack[0].m_obj;
uint8_t v_severity_1049_ = stack[1].m_num;
uint8_t v_isSilent_1050_ = stack[2].m_num;
lean_object* v___y_1051_ = stack[3].m_obj;
lean_object* v___y_1052_ = stack[4].m_obj;
lean_object* v___y_1053_ = stack[5].m_obj;
lean_object* v___y_1054_ = stack[6].m_obj;
lean_object* v___y_1055_ = stack[7].m_obj;
lean_object* v___y_1056_ = stack[8].m_obj;
lean_object* v_res_1060_;
v_res_1060_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v_msgData_1048_, v_severity_1049_, v_isSilent_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
stack->m_obj
 = v_res_1060_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(lean_object* v_msgData_1061_, lean_object* v_severity_1062_, lean_object* v_isSilent_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v_severity_boxed_1071_; uint8_t v_isSilent_boxed_1072_; lean_object* v_res_1073_; 
v_severity_boxed_1071_ = lean_unbox(v_severity_1062_);
v_isSilent_boxed_1072_ = lean_unbox(v_isSilent_1063_);
v_res_1073_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v_msgData_1061_, v_severity_boxed_1071_, v_isSilent_boxed_1072_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1073_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg(){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
v___x_1077_ = l_IO_CancelToken_isSet(v___x_1076_);
lean_dec_ref(v___x_1076_);
if (v___x_1077_ == 0)
{
uint32_t v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = 30;
v___x_1079_ = l_IO_sleep(v___x_1078_);
goto _start;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1075_);
return v___x_1081_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1082_;
v_res_1082_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1086_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_1087_ = lean_unsigned_to_nat(41u);
v___x_1088_ = lean_unsigned_to_nat(113u);
v___x_1089_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0));
v___x_1090_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_1091_ = l_mkPanicMessageWithDecl(v___x_1090_, v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_);
return v___x_1091_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(lean_object* v_x_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_toCold_1100_; lean_object* v_cancelTk_x3f_1101_; 
v_toCold_1100_ = lean_ctor_get(v___y_1097_, 0);
v_cancelTk_x3f_1101_ = lean_ctor_get(v_toCold_1100_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1101_) == 1)
{
lean_object* v_ref_1102_; lean_object* v_val_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_ref_1102_ = lean_ctor_get(v___y_1097_, 2);
v_val_1103_ = lean_ctor_get(v_cancelTk_x3f_1101_, 0);
v___x_1104_ = lean_box(0);
v___x_1105_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1131_; 
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1105_, 0);
lean_dec(v_unused_1132_);
v___x_1107_ = v___x_1105_;
v_isShared_1108_ = v_isSharedCheck_1131_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v___x_1105_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1131_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
uint8_t v___x_1109_; 
v___x_1109_ = l_IO_CancelToken_isSet(v_val_1103_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1111_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1104_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_del_object(v___x_1107_);
v___x_1113_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_1114_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; uint8_t v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref_known(v___x_1114_, 1);
v___x_1115_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_1116_ = 2;
v___x_1117_ = 0;
v___x_1118_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1115_, v___x_1116_, v___x_1117_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1118_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1130_; 
v_a_1119_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1121_ = v___x_1114_;
v_isShared_1122_ = v_isSharedCheck_1130_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1114_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1130_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1123_ = lean_io_error_to_string(v_a_1119_);
v___x_1124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_ofFormat(v___x_1124_);
lean_inc(v_ref_1102_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_ref_1102_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1126_);
v___x_1128_ = v___x_1121_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
return v___x_1105_;
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1);
v___x_1134_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1133_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1134_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1092_ = stack[0].m_obj;
lean_object* v___y_1093_ = stack[1].m_obj;
lean_object* v___y_1094_ = stack[2].m_obj;
lean_object* v___y_1095_ = stack[3].m_obj;
lean_object* v___y_1096_ = stack[4].m_obj;
lean_object* v___y_1097_ = stack[5].m_obj;
lean_object* v___y_1098_ = stack[6].m_obj;
lean_object* v_res_1135_;
v_res_1135_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(v_x_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
stack->m_obj
 = v_res_1135_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed(lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1144_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1153_);
return v___x_1154_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(lean_object* v_x_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1));
v___x_1166_ = l_Lean_Syntax_isOfKind(v_x_1155_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1167_;
}
else
{
lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___f_1168_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0));
v___x_1169_ = l_IO_CancelToken_new();
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
v___x_1171_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2));
v___x_1172_ = l_Lean_Name_toString(v___x_1171_, v___x_1166_);
lean_inc_ref(v___x_1170_);
v___x_1173_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1168_, v___x_1170_, v___x_1172_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_apply_1(v_a_1174_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_io_as_task(v___x_1176_, v___x_1177_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
lean_ctor_set(v___x_1181_, 2, v___x_1170_);
lean_ctor_set(v___x_1181_, 3, v___x_1178_);
v___x_1182_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1181_, v_a_1163_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref_known(v___x_1182_, 1);
v___x_1183_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1184_ = 2;
v___x_1185_ = 0;
v___x_1186_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1183_, v___x_1184_, v___x_1185_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1186_;
}
else
{
return v___x_1182_;
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref_known(v___x_1170_, 1);
v_a_1187_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1173_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1173_);
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
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1155_ = stack[0].m_obj;
lean_object* v_a_1156_ = stack[1].m_obj;
lean_object* v_a_1157_ = stack[2].m_obj;
lean_object* v_a_1158_ = stack[3].m_obj;
lean_object* v_a_1159_ = stack[4].m_obj;
lean_object* v_a_1160_ = stack[5].m_obj;
lean_object* v_a_1161_ = stack[6].m_obj;
lean_object* v_a_1162_ = stack[7].m_obj;
lean_object* v_a_1163_ = stack[8].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(v_x_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___boxed(lean_object* v_x_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(v_x_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
return v_res_1206_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_object* v_inst_1207_, lean_object* v_a_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v___x_1216_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1208_ = stack[1].m_obj;
lean_object* v___y_1209_ = stack[2].m_obj;
lean_object* v___y_1210_ = stack[3].m_obj;
lean_object* v___y_1211_ = stack[4].m_obj;
lean_object* v___y_1212_ = stack[5].m_obj;
lean_object* v___y_1213_ = stack[6].m_obj;
lean_object* v___y_1214_ = stack[7].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_box(0), v_a_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(lean_object* v_inst_1218_, lean_object* v_a_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(v_inst_1218_, v_a_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1227_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(lean_object* v_ref_1228_, lean_object* v_msgData_1229_, uint8_t v_severity_1230_, uint8_t v_isSilent_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1228_, v_msgData_1229_, v_severity_1230_, v_isSilent_1231_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1228_ = stack[0].m_obj;
lean_object* v_msgData_1229_ = stack[1].m_obj;
uint8_t v_severity_1230_ = stack[2].m_num;
uint8_t v_isSilent_1231_ = stack[3].m_num;
lean_object* v___y_1232_ = stack[4].m_obj;
lean_object* v___y_1233_ = stack[5].m_obj;
lean_object* v___y_1234_ = stack[6].m_obj;
lean_object* v___y_1235_ = stack[7].m_obj;
lean_object* v___y_1236_ = stack[8].m_obj;
lean_object* v___y_1237_ = stack[9].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(v_ref_1228_, v_msgData_1229_, v_severity_1230_, v_isSilent_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
stack->m_obj
 = v_res_1240_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___boxed(lean_object* v_ref_1241_, lean_object* v_msgData_1242_, lean_object* v_severity_1243_, lean_object* v_isSilent_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v_severity_boxed_1252_; uint8_t v_isSilent_boxed_1253_; lean_object* v_res_1254_; 
v_severity_boxed_1252_ = lean_unbox(v_severity_1243_);
v_isSilent_boxed_1253_ = lean_unbox(v_isSilent_1244_);
v_res_1254_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(v_ref_1241_, v_msgData_1242_, v_severity_boxed_1252_, v_isSilent_boxed_1253_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v_ref_1241_);
return v_res_1254_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
v___x_1282_ = l_IO_CancelToken_set(v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1271_ = stack[0].m_obj;
lean_object* v___y_1272_ = stack[1].m_obj;
lean_object* v___y_1273_ = stack[2].m_obj;
lean_object* v___y_1274_ = stack[3].m_obj;
lean_object* v___y_1275_ = stack[4].m_obj;
lean_object* v___y_1276_ = stack[5].m_obj;
lean_object* v___y_1277_ = stack[6].m_obj;
lean_object* v___y_1278_ = stack[7].m_obj;
lean_object* v___y_1279_ = stack[8].m_obj;
lean_object* v_res_1284_;
v_res_1284_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(v_x_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
stack->m_obj
 = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed(lean_object* v_x_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(v_x_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1295_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(lean_object* v_x_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1));
v___x_1309_ = l_Lean_Syntax_isOfKind(v_x_1298_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1310_;
}
else
{
lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_103__overap_1313_; lean_object* v___x_1314_; 
v___f_1311_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0));
v___x_1312_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1));
v___x_103__overap_1313_ = lean_dbg_trace(v___x_1312_, v___f_1311_);
lean_inc(v_a_1306_);
lean_inc_ref(v_a_1305_);
lean_inc(v_a_1304_);
lean_inc_ref(v_a_1303_);
lean_inc(v_a_1302_);
lean_inc_ref(v_a_1301_);
lean_inc(v_a_1300_);
lean_inc_ref(v_a_1299_);
v___x_1314_ = lean_apply_9(v___x_103__overap_1313_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, lean_box(0));
return v___x_1314_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1298_ = stack[0].m_obj;
lean_object* v_a_1299_ = stack[1].m_obj;
lean_object* v_a_1300_ = stack[2].m_obj;
lean_object* v_a_1301_ = stack[3].m_obj;
lean_object* v_a_1302_ = stack[4].m_obj;
lean_object* v_a_1303_ = stack[5].m_obj;
lean_object* v_a_1304_ = stack[6].m_obj;
lean_object* v_a_1305_ = stack[7].m_obj;
lean_object* v_a_1306_ = stack[8].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(v_x_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___boxed(lean_object* v_x_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(v_x_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1326_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1353_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1354_ = 2;
v___x_1355_ = 0;
v___x_1356_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1353_, v___x_1354_, v___x_1355_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1356_;
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1343_ = stack[0].m_obj;
lean_object* v___y_1344_ = stack[1].m_obj;
lean_object* v___y_1345_ = stack[2].m_obj;
lean_object* v___y_1346_ = stack[3].m_obj;
lean_object* v___y_1347_ = stack[4].m_obj;
lean_object* v___y_1348_ = stack[5].m_obj;
lean_object* v___y_1349_ = stack[6].m_obj;
lean_object* v___y_1350_ = stack[7].m_obj;
lean_object* v___y_1351_ = stack[8].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(v_x_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed(lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1368_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(lean_object* v_val_1369_){
_start:
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = l_IO_CancelToken_isSet(v_val_1369_);
if (v___x_1372_ == 0)
{
uint32_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = 30;
v___x_1374_ = l_IO_sleep(v___x_1373_);
goto _start;
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1371_);
return v___x_1376_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1369_ = stack[0].m_obj;
lean_object* v_res_1377_;
v_res_1377_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1369_);
stack->m_obj
 = v_res_1377_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(lean_object* v_val_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1378_);
lean_dec_ref(v_val_1378_);
return v_res_1380_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1382_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_1383_ = lean_unsigned_to_nat(41u);
v___x_1384_ = lean_unsigned_to_nat(147u);
v___x_1385_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0));
v___x_1386_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_1387_ = l_mkPanicMessageWithDecl(v___x_1386_, v___x_1385_, v___x_1384_, v___x_1383_, v___x_1382_);
return v___x_1387_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(lean_object* v_val_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_toCold_1397_; lean_object* v_cancelTk_x3f_1398_; 
v_toCold_1397_ = lean_ctor_get(v___y_1394_, 0);
v_cancelTk_x3f_1398_ = lean_ctor_get(v_toCold_1397_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1398_) == 1)
{
lean_object* v_ref_1399_; lean_object* v_val_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_ref_1399_ = lean_ctor_get(v___y_1394_, 2);
v_val_1400_ = lean_ctor_get(v_cancelTk_x3f_1398_, 0);
v___x_1401_ = lean_box(0);
v___x_1402_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1402_, 0);
lean_dec(v_unused_1438_);
v___x_1404_ = v___x_1402_;
v_isShared_1405_ = v_isSharedCheck_1437_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v___x_1402_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1437_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_1407_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
lean_dec_ref_known(v___x_1407_, 1);
lean_del_object(v___x_1404_);
v___x_1408_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_1409_ = 2;
v___x_1410_ = 0;
v___x_1411_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1408_, v___x_1409_, v___x_1410_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1411_, 0);
lean_dec(v_unused_1422_);
v___x_1413_ = v___x_1411_;
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
else
{
lean_dec(v___x_1411_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_io_promise_resolve(v___x_1401_, v_val_1388_);
v___x_1416_ = l_IO_CancelToken_isSet(v_val_1400_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1418_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1401_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1401_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
else
{
lean_object* v___x_1420_; 
lean_del_object(v___x_1413_);
v___x_1420_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1420_;
}
}
}
else
{
return v___x_1411_;
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1436_; 
v_a_1423_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1425_ = v___x_1407_;
v_isShared_1426_ = v_isSharedCheck_1436_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1407_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1436_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_io_error_to_string(v_a_1423_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 3);
lean_ctor_set(v___x_1404_, 0, v___x_1427_);
v___x_1429_ = v___x_1404_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = l_Lean_MessageData_ofFormat(v___x_1429_);
lean_inc(v_ref_1399_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_ref_1399_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1431_);
v___x_1433_ = v___x_1425_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
else
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1);
v___x_1440_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1439_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1440_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1388_ = stack[0].m_obj;
lean_object* v_x_1389_ = stack[1].m_obj;
lean_object* v___y_1390_ = stack[2].m_obj;
lean_object* v___y_1391_ = stack[3].m_obj;
lean_object* v___y_1392_ = stack[4].m_obj;
lean_object* v___y_1393_ = stack[5].m_obj;
lean_object* v___y_1394_ = stack[6].m_obj;
lean_object* v___y_1395_ = stack[7].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(v_val_1388_, v_x_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(v_val_1442_, v_x_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_val_1442_);
return v_res_1451_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(lean_object* v_x_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1));
v___x_1471_ = l_Lean_Syntax_isOfKind(v_x_1460_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1472_;
}
else
{
lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___y_1479_; 
v___f_1473_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
v___x_1474_ = lean_io_promise_new();
lean_inc(v___x_1474_);
v___f_1475_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed), 9, 1);
lean_closure_set(v___f_1475_, 0, v___x_1474_);
v___x_1476_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1477_ = lean_st_ref_take(v___x_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = l_IO_Promise_result_x21___redArg(v___x_1474_);
lean_dec(v___x_1474_);
v___y_1479_ = v___x_1517_;
goto v___jp_1478_;
}
else
{
lean_object* v_val_1518_; 
lean_dec(v___x_1474_);
v_val_1518_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_val_1518_);
v___y_1479_ = v_val_1518_;
goto v___jp_1478_;
}
v___jp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___y_1479_);
v___x_1481_ = lean_st_ref_put(v___x_1476_, v___x_1480_);
if (lean_obj_tag(v___x_1477_) == 1)
{
lean_object* v_val_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v___f_1475_);
v_val_1482_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1484_ = v___x_1477_;
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_val_1482_);
lean_dec(v___x_1477_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1486_ = lean_io_wait(v_val_1482_);
lean_dec(v___x_1486_);
v___x_1487_ = lean_box(0);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v___x_1477_);
v___x_1492_ = l_IO_CancelToken_new();
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
v___x_1494_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2));
v___x_1495_ = l_Lean_Name_toString(v___x_1494_, v___x_1471_);
lean_inc_ref(v___x_1493_);
v___x_1496_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1475_, v___x_1493_, v___x_1495_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_apply_1(v_a_1497_, v___x_1498_);
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_io_as_task(v___x_1499_, v___x_1500_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
lean_ctor_set(v___x_1504_, 2, v___x_1493_);
lean_ctor_set(v___x_1504_, 3, v___x_1501_);
v___x_1505_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1504_, v_a_1468_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_7025__overap_1507_; lean_object* v___x_1508_; 
lean_dec_ref_known(v___x_1505_, 1);
v___x_1506_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_7025__overap_1507_ = lean_dbg_trace(v___x_1506_, v___f_1473_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
lean_inc(v_a_1466_);
lean_inc_ref(v_a_1465_);
lean_inc(v_a_1464_);
lean_inc_ref(v_a_1463_);
lean_inc(v_a_1462_);
lean_inc_ref(v_a_1461_);
v___x_1508_ = lean_apply_9(v___x_7025__overap_1507_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, lean_box(0));
return v___x_1508_;
}
else
{
return v___x_1505_;
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref_known(v___x_1493_, 1);
v_a_1509_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1496_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1496_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1460_ = stack[0].m_obj;
lean_object* v_a_1461_ = stack[1].m_obj;
lean_object* v_a_1462_ = stack[2].m_obj;
lean_object* v_a_1463_ = stack[3].m_obj;
lean_object* v_a_1464_ = stack[4].m_obj;
lean_object* v_a_1465_ = stack[5].m_obj;
lean_object* v_a_1466_ = stack[6].m_obj;
lean_object* v_a_1467_ = stack[7].m_obj;
lean_object* v_a_1468_ = stack[8].m_obj;
lean_object* v_res_1519_;
v_res_1519_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(v_x_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
stack->m_obj
 = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___boxed(lean_object* v_x_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(v_x_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
return v_res_1530_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(lean_object* v_val_1531_, lean_object* v_inst_1532_, lean_object* v_a_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1531_);
return v___x_1541_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1531_ = stack[0].m_obj;
lean_object* v_a_1533_ = stack[2].m_obj;
lean_object* v___y_1534_ = stack[3].m_obj;
lean_object* v___y_1535_ = stack[4].m_obj;
lean_object* v___y_1536_ = stack[5].m_obj;
lean_object* v___y_1537_ = stack[6].m_obj;
lean_object* v___y_1538_ = stack[7].m_obj;
lean_object* v___y_1539_ = stack[8].m_obj;
lean_object* v_res_1542_;
v_res_1542_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(v_val_1531_, lean_box(0), v_a_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
stack->m_obj
 = v_res_1542_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(lean_object* v_val_1543_, lean_object* v_inst_1544_, lean_object* v_a_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(v_val_1543_, v_inst_1544_, v_a_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_val_1543_);
return v_res_1553_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(lean_object* v_val_1570_, lean_object* v_val_1571_, lean_object* v_x_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1570_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1623_; 
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1581_, 0);
lean_dec(v_unused_1624_);
v___x_1583_ = v___x_1581_;
v_isShared_1584_ = v_isSharedCheck_1623_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v___x_1581_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1623_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_toCold_1585_; lean_object* v_ref_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_toCold_1585_ = lean_ctor_get(v___y_1577_, 0);
v_ref_1586_ = lean_ctor_get(v___y_1577_, 2);
v___x_1587_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_1588_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; uint8_t v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
lean_dec_ref_known(v___x_1588_, 1);
lean_del_object(v___x_1583_);
v___x_1589_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_1590_ = 2;
v___x_1591_ = 0;
v___x_1592_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1589_, v___x_1590_, v___x_1591_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1592_, 0);
lean_dec(v_unused_1608_);
v___x_1594_ = v___x_1592_;
v_isShared_1595_ = v_isSharedCheck_1607_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v___x_1592_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1607_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v_cancelTk_x3f_1597_; 
v___x_1596_ = lean_io_promise_resolve(v___x_1580_, v_val_1571_);
v_cancelTk_x3f_1597_ = lean_ctor_get(v_toCold_1585_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1597_) == 1)
{
lean_object* v_val_1598_; uint8_t v___x_1599_; 
v_val_1598_ = lean_ctor_get(v_cancelTk_x3f_1597_, 0);
v___x_1599_ = l_IO_CancelToken_isSet(v_val_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1601_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1580_);
v___x_1601_ = v___x_1594_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1580_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
else
{
lean_object* v___x_1603_; 
lean_del_object(v___x_1594_);
v___x_1603_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1603_;
}
}
else
{
lean_object* v___x_1605_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1580_);
v___x_1605_ = v___x_1594_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1580_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
return v___x_1592_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1622_; 
v_a_1609_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1611_ = v___x_1588_;
v_isShared_1612_ = v_isSharedCheck_1622_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1588_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1622_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_io_error_to_string(v_a_1609_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 3);
lean_ctor_set(v___x_1583_, 0, v___x_1613_);
v___x_1615_ = v___x_1583_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1616_ = l_Lean_MessageData_ofFormat(v___x_1615_);
lean_inc(v_ref_1586_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_ref_1586_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1617_);
v___x_1619_ = v___x_1611_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
else
{
return v___x_1581_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1570_ = stack[0].m_obj;
lean_object* v_val_1571_ = stack[1].m_obj;
lean_object* v_x_1572_ = stack[2].m_obj;
lean_object* v___y_1573_ = stack[3].m_obj;
lean_object* v___y_1574_ = stack[4].m_obj;
lean_object* v___y_1575_ = stack[5].m_obj;
lean_object* v___y_1576_ = stack[6].m_obj;
lean_object* v___y_1577_ = stack[7].m_obj;
lean_object* v___y_1578_ = stack[8].m_obj;
lean_object* v_res_1625_;
v_res_1625_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(v_val_1570_, v_val_1571_, v_x_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
stack->m_obj
 = v_res_1625_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1626_, lean_object* v_val_1627_, lean_object* v_x_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(v_val_1626_, v_val_1627_, v_x_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v_val_1627_);
lean_dec_ref(v_val_1626_);
return v_res_1636_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1647_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_1648_ = lean_unsigned_to_nat(60u);
v___x_1649_ = lean_unsigned_to_nat(177u);
v___x_1650_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3));
v___x_1651_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_1652_ = l_mkPanicMessageWithDecl(v___x_1651_, v___x_1650_, v___x_1649_, v___x_1648_, v___x_1647_);
return v___x_1652_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(lean_object* v_x_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1));
v___x_1664_ = l_Lean_Syntax_isOfKind(v_x_1653_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1665_;
}
else
{
lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___y_1671_; 
v___f_1666_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
v___x_1667_ = lean_io_promise_new();
v___x_1668_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1669_ = lean_st_ref_take(v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v___x_1713_; 
v___x_1713_ = l_IO_Promise_result_x21___redArg(v___x_1667_);
v___y_1671_ = v___x_1713_;
goto v___jp_1670_;
}
else
{
lean_object* v_val_1714_; 
v_val_1714_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_val_1714_);
v___y_1671_ = v_val_1714_;
goto v___jp_1670_;
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1671_);
v___x_1673_ = lean_st_ref_put(v___x_1668_, v___x_1672_);
if (lean_obj_tag(v___x_1669_) == 1)
{
lean_object* v_val_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v___x_1667_);
v_val_1674_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1676_ = v___x_1669_;
v_isShared_1677_ = v_isSharedCheck_1683_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_val_1674_);
lean_dec(v___x_1669_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1683_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = lean_io_wait(v_val_1674_);
lean_dec(v___x_1678_);
v___x_1679_ = lean_box(0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1679_);
v___x_1681_ = v___x_1676_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_object* v_toCold_1684_; lean_object* v_cancelTk_x3f_1685_; 
lean_dec(v___x_1669_);
v_toCold_1684_ = lean_ctor_get(v_a_1660_, 0);
v_cancelTk_x3f_1685_ = lean_ctor_get(v_toCold_1684_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1685_) == 1)
{
lean_object* v_val_1686_; lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_val_1686_ = lean_ctor_get(v_cancelTk_x3f_1685_, 0);
lean_inc(v_val_1686_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed), 10, 2);
lean_closure_set(v___f_1687_, 0, v_val_1686_);
lean_closure_set(v___f_1687_, 1, v___x_1667_);
v___x_1688_ = lean_box(0);
v___x_1689_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1));
v___x_1690_ = l_Lean_Name_toString(v___x_1689_, v___x_1664_);
v___x_1691_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1687_, v___x_1688_, v___x_1690_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_apply_1(v_a_1692_, v___x_1693_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_io_as_task(v___x_1694_, v___x_1695_);
v___x_1697_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_1685_);
v___x_1698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1688_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
lean_ctor_set(v___x_1698_, 2, v_cancelTk_x3f_1685_);
lean_ctor_set(v___x_1698_, 3, v___x_1696_);
v___x_1699_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1698_, v_a_1661_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; lean_object* v___x_6901__overap_1701_; lean_object* v___x_1702_; 
lean_dec_ref_known(v___x_1699_, 1);
v___x_1700_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_6901__overap_1701_ = lean_dbg_trace(v___x_1700_, v___f_1666_);
lean_inc(v_a_1661_);
lean_inc_ref(v_a_1660_);
lean_inc(v_a_1659_);
lean_inc_ref(v_a_1658_);
lean_inc(v_a_1657_);
lean_inc_ref(v_a_1656_);
lean_inc(v_a_1655_);
lean_inc_ref(v_a_1654_);
v___x_1702_ = lean_apply_9(v___x_6901__overap_1701_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, lean_box(0));
return v___x_1702_;
}
else
{
return v___x_1699_;
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_a_1703_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1691_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1691_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v___x_1667_);
v___x_1711_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4);
v___x_1712_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_1711_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
return v___x_1712_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1653_ = stack[0].m_obj;
lean_object* v_a_1654_ = stack[1].m_obj;
lean_object* v_a_1655_ = stack[2].m_obj;
lean_object* v_a_1656_ = stack[3].m_obj;
lean_object* v_a_1657_ = stack[4].m_obj;
lean_object* v_a_1658_ = stack[5].m_obj;
lean_object* v_a_1659_ = stack[6].m_obj;
lean_object* v_a_1660_ = stack[7].m_obj;
lean_object* v_a_1661_ = stack[8].m_obj;
lean_object* v_res_1715_;
v_res_1715_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(v_x_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
stack->m_obj
 = v_res_1715_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___boxed(lean_object* v_x_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(v_x_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1726_;
}
}
lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_st_mk_ref(v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1731_;
v_res_1731_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1731_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
return v_res_1733_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg(){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1764_;
v_res_1764_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
stack->m_obj
 = v_res_1764_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg___boxed(lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v_res_1766_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(lean_object* v_00_u03b1_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_1771_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1768_ = stack[1].m_obj;
lean_object* v___y_1769_ = stack[2].m_obj;
lean_object* v_res_1772_;
v_res_1772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(lean_box(0), v___y_1768_, v___y_1769_);
stack->m_obj
 = v_res_1772_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___boxed(lean_object* v_00_u03b1_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(v_00_u03b1_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1777_;
}
}
lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___f_1783_; lean_object* v___x_3922__overap_1784_; lean_object* v___x_1785_; 
v___f_1783_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0));
v___x_3922__overap_1784_ = lean_panic_fn_borrowed(v___f_1783_, v_msg_1779_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
v___x_1785_ = lean_apply_3(v___x_3922__overap_1784_, v___y_1780_, v___y_1781_, lean_box(0));
return v___x_1785_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1779_ = stack[0].m_obj;
lean_object* v___y_1780_ = stack[1].m_obj;
lean_object* v___y_1781_ = stack[2].m_obj;
lean_object* v_res_1786_;
v_res_1786_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v_msg_1779_, v___y_1780_, v___y_1781_);
stack->m_obj
 = v_res_1786_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___boxed(lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v_msg_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1791_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1796_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
lean_ctor_set(v___x_1798_, 2, v___x_1797_);
lean_ctor_set(v___x_1798_, 3, v___x_1797_);
lean_ctor_set(v___x_1798_, 4, v___x_1796_);
lean_ctor_set(v___x_1798_, 5, v___x_1796_);
lean_ctor_set(v___x_1798_, 6, v___x_1796_);
lean_ctor_set(v___x_1798_, 7, v___x_1796_);
lean_ctor_set(v___x_1798_, 8, v___x_1796_);
lean_ctor_set(v___x_1798_, 9, v___x_1796_);
lean_ctor_set(v___x_1798_, 10, v___x_1796_);
lean_ctor_set(v___x_1798_, 11, v___x_1795_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_unsigned_to_nat(32u);
v___x_1800_ = lean_mk_empty_array_with_capacity(v___x_1799_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1802_ = ((size_t)5ULL);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_unsigned_to_nat(32u);
v___x_1805_ = lean_mk_empty_array_with_capacity(v___x_1804_);
v___x_1806_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3);
v___x_1807_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1805_);
lean_ctor_set(v___x_1807_, 2, v___x_1803_);
lean_ctor_set(v___x_1807_, 3, v___x_1803_);
lean_ctor_set_usize(v___x_1807_, 4, v___x_1802_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_box(1);
v___x_1809_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4);
v___x_1810_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v___x_1809_);
lean_ctor_set(v___x_1811_, 2, v___x_1808_);
return v___x_1811_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(lean_object* v_msgData_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_toCold_1817_; lean_object* v_env_1818_; lean_object* v_options_1819_; uint8_t v___x_1820_; lean_object* v_env_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1816_ = lean_st_ref_get(v___y_1814_);
v_toCold_1817_ = lean_ctor_get(v___y_1813_, 0);
v_env_1818_ = lean_ctor_get(v___x_1816_, 0);
lean_inc_ref(v_env_1818_);
lean_dec(v___x_1816_);
v_options_1819_ = lean_ctor_get(v_toCold_1817_, 2);
v___x_1820_ = 0;
v_env_1821_ = l_Lean_Environment_setRecordingDeps(v_env_1818_, v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_1823_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5);
lean_inc_ref(v_options_1819_);
v___x_1824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1824_, 0, v_env_1821_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
lean_ctor_set(v___x_1824_, 3, v_options_1819_);
v___x_1825_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v_msgData_1812_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1812_ = stack[0].m_obj;
lean_object* v___y_1813_ = stack[1].m_obj;
lean_object* v___y_1814_ = stack[2].m_obj;
lean_object* v_res_1827_;
v_res_1827_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v_msgData_1812_, v___y_1813_, v___y_1814_);
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v_msgData_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1832_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(lean_object* v_ref_1833_, lean_object* v_msgData_1834_, uint8_t v_severity_1835_, uint8_t v_isSilent_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; uint8_t v___y_1847_; lean_object* v_toCold_1848_; lean_object* v___y_1849_; lean_object* v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1905_; uint8_t v___y_1906_; lean_object* v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1915_; uint8_t v___y_1916_; uint8_t v___y_1917_; uint8_t v___x_1928_; uint8_t v___y_1930_; uint8_t v___y_1931_; uint8_t v___y_1932_; uint8_t v___y_1934_; uint8_t v___x_1942_; 
v___x_1928_ = 2;
v___x_1942_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1835_, v___x_1928_);
if (v___x_1942_ == 0)
{
v___y_1934_ = v___x_1942_;
goto v___jp_1933_;
}
else
{
uint8_t v___x_1943_; 
lean_inc_ref(v_msgData_1834_);
v___x_1943_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1834_);
v___y_1934_ = v___x_1943_;
goto v___jp_1933_;
}
v___jp_1840_:
{
lean_object* v_currNamespace_1850_; lean_object* v_openDecls_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_env_1856_; lean_object* v_nextMacroScope_1857_; lean_object* v_ngen_1858_; lean_object* v_auxDeclNGen_1859_; lean_object* v_traceState_1860_; lean_object* v_cache_1861_; lean_object* v_recordedDeps_1862_; lean_object* v_messages_1863_; lean_object* v_infoState_1864_; lean_object* v_snapshotTasks_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1876_; 
v_currNamespace_1850_ = lean_ctor_get(v_toCold_1848_, 4);
v_openDecls_1851_ = lean_ctor_get(v_toCold_1848_, 5);
lean_inc(v_openDecls_1851_);
lean_inc(v_currNamespace_1850_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_currNamespace_1850_);
lean_ctor_set(v___x_1852_, 1, v_openDecls_1851_);
v___x_1853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___y_1842_);
lean_inc_ref(v___y_1846_);
lean_inc_ref(v___y_1844_);
v___x_1854_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1854_, 0, v___y_1844_);
lean_ctor_set(v___x_1854_, 1, v___y_1845_);
lean_ctor_set(v___x_1854_, 2, v___y_1843_);
lean_ctor_set(v___x_1854_, 3, v___y_1846_);
lean_ctor_set(v___x_1854_, 4, v___x_1853_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*5, v___y_1847_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*5 + 1, v___y_1841_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*5 + 2, v_isSilent_1836_);
v___x_1855_ = lean_st_ref_take(v___y_1849_);
v_env_1856_ = lean_ctor_get(v___x_1855_, 0);
v_nextMacroScope_1857_ = lean_ctor_get(v___x_1855_, 1);
v_ngen_1858_ = lean_ctor_get(v___x_1855_, 2);
v_auxDeclNGen_1859_ = lean_ctor_get(v___x_1855_, 3);
v_traceState_1860_ = lean_ctor_get(v___x_1855_, 4);
v_cache_1861_ = lean_ctor_get(v___x_1855_, 5);
v_recordedDeps_1862_ = lean_ctor_get(v___x_1855_, 6);
v_messages_1863_ = lean_ctor_get(v___x_1855_, 7);
v_infoState_1864_ = lean_ctor_get(v___x_1855_, 8);
v_snapshotTasks_1865_ = lean_ctor_get(v___x_1855_, 9);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1867_ = v___x_1855_;
v_isShared_1868_ = v_isSharedCheck_1876_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snapshotTasks_1865_);
lean_inc(v_infoState_1864_);
lean_inc(v_messages_1863_);
lean_inc(v_recordedDeps_1862_);
lean_inc(v_cache_1861_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1859_);
lean_inc(v_ngen_1858_);
lean_inc(v_nextMacroScope_1857_);
lean_inc(v_env_1856_);
lean_dec(v___x_1855_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1876_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = l_Lean_MessageLog_add(v___x_1854_, v_messages_1863_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 7, v___x_1870_);
v___x_1872_ = v___x_1867_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_env_1856_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_nextMacroScope_1857_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_ngen_1858_);
lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_auxDeclNGen_1859_);
lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_traceState_1860_);
lean_ctor_set(v_reuseFailAlloc_1875_, 5, v_cache_1861_);
lean_ctor_set(v_reuseFailAlloc_1875_, 6, v_recordedDeps_1862_);
lean_ctor_set(v_reuseFailAlloc_1875_, 7, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1875_, 8, v_infoState_1864_);
lean_ctor_set(v_reuseFailAlloc_1875_, 9, v_snapshotTasks_1865_);
v___x_1872_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_st_ref_put(v___y_1849_, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1869_);
return v___x_1874_;
}
}
}
v___jp_1877_:
{
lean_object* v_fileName_1886_; lean_object* v_fileMap_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1903_; 
v_fileName_1886_ = lean_ctor_get(v___y_1883_, 0);
v_fileMap_1887_ = lean_ctor_get(v___y_1883_, 1);
v___x_1888_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1834_);
v___x_1889_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v___x_1888_, v___y_1837_, v___y_1838_);
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1903_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1903_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_inc_ref_n(v_fileMap_1887_, 2);
v___x_1894_ = l_Lean_FileMap_toPosition(v_fileMap_1887_, v___y_1882_);
lean_dec(v___y_1882_);
v___x_1895_ = l_Lean_FileMap_toPosition(v_fileMap_1887_, v___y_1885_);
lean_dec(v___y_1885_);
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
v___x_1897_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_1881_ == 0)
{
lean_del_object(v___x_1892_);
lean_dec_ref(v___y_1878_);
v___y_1841_ = v___y_1880_;
v___y_1842_ = v_a_1890_;
v___y_1843_ = v___x_1896_;
v___y_1844_ = v_fileName_1886_;
v___y_1845_ = v___x_1894_;
v___y_1846_ = v___x_1897_;
v___y_1847_ = v___y_1884_;
v_toCold_1848_ = v___y_1879_;
v___y_1849_ = v___y_1838_;
goto v___jp_1840_;
}
else
{
uint8_t v___x_1898_; 
lean_inc(v_a_1890_);
v___x_1898_ = l_Lean_MessageData_hasTag(v___y_1878_, v_a_1890_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec_ref_known(v___x_1896_, 1);
lean_dec_ref(v___x_1894_);
lean_dec(v_a_1890_);
v___x_1899_ = lean_box(0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1899_);
v___x_1901_ = v___x_1892_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
else
{
lean_del_object(v___x_1892_);
v___y_1841_ = v___y_1880_;
v___y_1842_ = v_a_1890_;
v___y_1843_ = v___x_1896_;
v___y_1844_ = v_fileName_1886_;
v___y_1845_ = v___x_1894_;
v___y_1846_ = v___x_1897_;
v___y_1847_ = v___y_1884_;
v_toCold_1848_ = v___y_1879_;
v___y_1849_ = v___y_1838_;
goto v___jp_1840_;
}
}
}
}
v___jp_1904_:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Syntax_getTailPos_x3f(v___y_1909_, v___y_1910_);
lean_dec(v___y_1909_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_inc(v___y_1911_);
v___y_1878_ = v___y_1905_;
v___y_1879_ = v___y_1907_;
v___y_1880_ = v___y_1908_;
v___y_1881_ = v___y_1906_;
v___y_1882_ = v___y_1911_;
v___y_1883_ = v___y_1907_;
v___y_1884_ = v___y_1910_;
v___y_1885_ = v___y_1911_;
goto v___jp_1877_;
}
else
{
lean_object* v_val_1913_; 
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___y_1878_ = v___y_1905_;
v___y_1879_ = v___y_1907_;
v___y_1880_ = v___y_1908_;
v___y_1881_ = v___y_1906_;
v___y_1882_ = v___y_1911_;
v___y_1883_ = v___y_1907_;
v___y_1884_ = v___y_1910_;
v___y_1885_ = v_val_1913_;
goto v___jp_1877_;
}
}
v___jp_1914_:
{
lean_object* v_toCold_1918_; lean_object* v_ref_1919_; uint8_t v_suppressElabErrors_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v_ref_1924_; lean_object* v___x_1925_; 
v_toCold_1918_ = lean_ctor_get(v___y_1837_, 0);
v_ref_1919_ = lean_ctor_get(v___y_1837_, 2);
v_suppressElabErrors_1920_ = lean_ctor_get_uint8(v___y_1837_, sizeof(void*)*3 + 2);
v___x_1921_ = lean_box(v_suppressElabErrors_1920_);
v___x_1922_ = lean_box(v___y_1915_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1923_, 0, v___x_1921_);
lean_closure_set(v___f_1923_, 1, v___x_1922_);
v_ref_1924_ = l_Lean_replaceRef(v_ref_1833_, v_ref_1919_);
v___x_1925_ = l_Lean_Syntax_getPos_x3f(v_ref_1924_, v___y_1916_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___y_1905_ = v___f_1923_;
v___y_1906_ = v_suppressElabErrors_1920_;
v___y_1907_ = v_toCold_1918_;
v___y_1908_ = v___y_1917_;
v___y_1909_ = v_ref_1924_;
v___y_1910_ = v___y_1916_;
v___y_1911_ = v___x_1926_;
goto v___jp_1904_;
}
else
{
lean_object* v_val_1927_; 
v_val_1927_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v___x_1925_, 1);
v___y_1905_ = v___f_1923_;
v___y_1906_ = v_suppressElabErrors_1920_;
v___y_1907_ = v_toCold_1918_;
v___y_1908_ = v___y_1917_;
v___y_1909_ = v_ref_1924_;
v___y_1910_ = v___y_1916_;
v___y_1911_ = v_val_1927_;
goto v___jp_1904_;
}
}
v___jp_1929_:
{
if (v___y_1932_ == 0)
{
v___y_1915_ = v___y_1930_;
v___y_1916_ = v___y_1931_;
v___y_1917_ = v_severity_1835_;
goto v___jp_1914_;
}
else
{
v___y_1915_ = v___y_1930_;
v___y_1916_ = v___y_1931_;
v___y_1917_ = v___x_1928_;
goto v___jp_1914_;
}
}
v___jp_1933_:
{
if (v___y_1934_ == 0)
{
uint8_t v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = 1;
v___x_1936_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1835_, v___x_1935_);
if (v___x_1936_ == 0)
{
v___y_1930_ = v___y_1934_;
v___y_1931_ = v___y_1934_;
v___y_1932_ = v___x_1936_;
goto v___jp_1929_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1837_);
v___x_1938_ = l_Lean_warningAsError;
v___x_1939_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v___x_1937_, v___x_1938_);
lean_dec_ref(v___x_1937_);
v___y_1930_ = v___y_1934_;
v___y_1931_ = v___y_1934_;
v___y_1932_ = v___x_1939_;
goto v___jp_1929_;
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v_msgData_1834_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1833_ = stack[0].m_obj;
lean_object* v_msgData_1834_ = stack[1].m_obj;
uint8_t v_severity_1835_ = stack[2].m_num;
uint8_t v_isSilent_1836_ = stack[3].m_num;
lean_object* v___y_1837_ = stack[4].m_obj;
lean_object* v___y_1838_ = stack[5].m_obj;
lean_object* v_res_1944_;
v_res_1944_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1833_, v_msgData_1834_, v_severity_1835_, v_isSilent_1836_, v___y_1837_, v___y_1838_);
stack->m_obj
 = v_res_1944_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_1945_, lean_object* v_msgData_1946_, lean_object* v_severity_1947_, lean_object* v_isSilent_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v_severity_boxed_1952_; uint8_t v_isSilent_boxed_1953_; lean_object* v_res_1954_; 
v_severity_boxed_1952_ = lean_unbox(v_severity_1947_);
v_isSilent_boxed_1953_ = lean_unbox(v_isSilent_1948_);
v_res_1954_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1945_, v_msgData_1946_, v_severity_boxed_1952_, v_isSilent_boxed_1953_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_ref_1945_);
return v_res_1954_;
}
}
lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(lean_object* v_msgData_1955_, uint8_t v_severity_1956_, uint8_t v_isSilent_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_ref_1961_; lean_object* v___x_1962_; 
v_ref_1961_ = lean_ctor_get(v___y_1958_, 2);
v___x_1962_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1961_, v_msgData_1955_, v_severity_1956_, v_isSilent_1957_, v___y_1958_, v___y_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1955_ = stack[0].m_obj;
uint8_t v_severity_1956_ = stack[1].m_num;
uint8_t v_isSilent_1957_ = stack[2].m_num;
lean_object* v___y_1958_ = stack[3].m_obj;
lean_object* v___y_1959_ = stack[4].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1955_, v_severity_1956_, v_isSilent_1957_, v___y_1958_, v___y_1959_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2___boxed(lean_object* v_msgData_1964_, lean_object* v_severity_1965_, lean_object* v_isSilent_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
uint8_t v_severity_boxed_1970_; uint8_t v_isSilent_boxed_1971_; lean_object* v_res_1972_; 
v_severity_boxed_1970_ = lean_unbox(v_severity_1965_);
v_isSilent_boxed_1971_ = lean_unbox(v_isSilent_1966_);
v_res_1972_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1964_, v_severity_boxed_1970_, v_isSilent_boxed_1971_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(lean_object* v_msgData_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = 0;
v___x_1978_ = 0;
v___x_1979_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1973_, v___x_1977_, v___x_1978_, v___y_1974_, v___y_1975_);
return v___x_1979_;
}
}
LEAN_EXPORT void l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1973_ = stack[0].m_obj;
lean_object* v___y_1974_ = stack[1].m_obj;
lean_object* v___y_1975_ = stack[2].m_obj;
lean_object* v_res_1980_;
v_res_1980_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v_msgData_1973_, v___y_1974_, v___y_1975_);
stack->m_obj
 = v_res_1980_;
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2___boxed(lean_object* v_msgData_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v_msgData_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1985_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(lean_object* v_val_1986_){
_start:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = l_IO_CancelToken_isSet(v_val_1986_);
if (v___x_1989_ == 0)
{
uint32_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = 30;
v___x_1991_ = l_IO_sleep(v___x_1990_);
goto _start;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1988_);
return v___x_1993_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1986_ = stack[0].m_obj;
lean_object* v_res_1994_;
v_res_1994_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1986_);
stack->m_obj
 = v_res_1994_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(lean_object* v_val_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1995_);
lean_dec_ref(v_val_1995_);
return v_res_1997_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(lean_object* v_val_1998_, lean_object* v_val_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1998_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2005_, 0);
lean_dec(v_unused_2046_);
v___x_2007_ = v___x_2005_;
v_isShared_2008_ = v_isSharedCheck_2045_;
goto v_resetjp_2006_;
}
else
{
lean_dec(v___x_2005_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2045_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_toCold_2009_; lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_toCold_2009_ = lean_ctor_get(v___y_2001_, 0);
v_ref_2010_ = lean_ctor_get(v___y_2001_, 2);
v___x_2011_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_2012_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2011_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref_known(v___x_2012_, 1);
lean_del_object(v___x_2007_);
v___x_2013_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_2014_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_2013_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2029_; 
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2014_, 0);
lean_dec(v_unused_2030_);
v___x_2016_ = v___x_2014_;
v_isShared_2017_ = v_isSharedCheck_2029_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v___x_2014_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2029_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v_cancelTk_x3f_2019_; 
v___x_2018_ = lean_io_promise_resolve(v___x_2004_, v_val_1999_);
v_cancelTk_x3f_2019_ = lean_ctor_get(v_toCold_2009_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2019_) == 1)
{
lean_object* v_val_2020_; uint8_t v___x_2021_; 
v_val_2020_ = lean_ctor_get(v_cancelTk_x3f_2019_, 0);
v___x_2021_ = l_IO_CancelToken_isSet(v_val_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2023_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2004_);
v___x_2023_ = v___x_2016_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2004_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
else
{
lean_object* v___x_2025_; 
lean_del_object(v___x_2016_);
v___x_2025_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_2025_;
}
}
else
{
lean_object* v___x_2027_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2004_);
v___x_2027_ = v___x_2016_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2004_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
return v___x_2014_;
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2044_; 
v_a_2031_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2033_ = v___x_2012_;
v_isShared_2034_ = v_isSharedCheck_2044_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2012_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2044_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = lean_io_error_to_string(v_a_2031_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set_tag(v___x_2007_, 3);
lean_ctor_set(v___x_2007_, 0, v___x_2035_);
v___x_2037_ = v___x_2007_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = l_Lean_MessageData_ofFormat(v___x_2037_);
lean_inc(v_ref_2010_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_ref_2010_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2039_);
v___x_2041_ = v___x_2033_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
else
{
return v___x_2005_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1998_ = stack[0].m_obj;
lean_object* v_val_1999_ = stack[1].m_obj;
lean_object* v_x_2000_ = stack[2].m_obj;
lean_object* v___y_2001_ = stack[3].m_obj;
lean_object* v___y_2002_ = stack[4].m_obj;
lean_object* v_res_2047_;
v_res_2047_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(v_val_1998_, v_val_1999_, v_x_2000_, v___y_2001_, v___y_2002_);
stack->m_obj
 = v_res_2047_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed(lean_object* v_val_2048_, lean_object* v_val_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(v_val_2048_, v_val_2049_, v_x_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v_val_2049_);
lean_dec_ref(v_val_2048_);
return v_res_2054_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2057_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_2058_ = lean_unsigned_to_nat(44u);
v___x_2059_ = lean_unsigned_to_nat(209u);
v___x_2060_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1));
v___x_2061_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_2062_ = l_mkPanicMessageWithDecl(v___x_2061_, v___x_2060_, v___x_2059_, v___x_2058_, v___x_2057_);
return v___x_2062_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(lean_object* v___x_2063_, lean_object* v___x_2064_, lean_object* v___x_2065_, lean_object* v___x_2066_, uint8_t v___x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___y_2075_; 
v___x_2071_ = lean_io_promise_new();
v___x_2072_ = l_Lean_Server_Test_Cancel_cmdOnceRef;
v___x_2073_ = lean_st_ref_take(v___x_2072_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v___x_2117_; 
v___x_2117_ = l_IO_Promise_result_x21___redArg(v___x_2071_);
v___y_2075_ = v___x_2117_;
goto v___jp_2074_;
}
else
{
lean_object* v_val_2118_; 
v_val_2118_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_val_2118_);
v___y_2075_ = v_val_2118_;
goto v___jp_2074_;
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___y_2075_);
v___x_2077_ = lean_st_ref_put(v___x_2072_, v___x_2076_);
if (lean_obj_tag(v___x_2073_) == 1)
{
lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v___x_2071_);
lean_dec_ref(v___y_2068_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2063_);
v_val_2078_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2080_ = v___x_2073_;
v_isShared_2081_ = v_isSharedCheck_2087_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_dec(v___x_2073_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2087_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2082_ = lean_io_wait(v_val_2078_);
lean_dec(v___x_2082_);
v___x_2083_ = lean_box(0);
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2083_);
v___x_2085_ = v___x_2080_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_toCold_2088_; lean_object* v_cancelTk_x3f_2089_; 
lean_dec(v___x_2073_);
v_toCold_2088_ = lean_ctor_get(v___y_2068_, 0);
v_cancelTk_x3f_2089_ = lean_ctor_get(v_toCold_2088_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2089_) == 1)
{
lean_object* v_val_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_val_2090_ = lean_ctor_get(v_cancelTk_x3f_2089_, 0);
lean_inc(v_val_2090_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_2091_, 0, v_val_2090_);
lean_closure_set(v___f_2091_, 1, v___x_2071_);
v___x_2092_ = lean_box(0);
v___x_2093_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0));
v___x_2094_ = l_Lean_Name_mkStr5(v___x_2063_, v___x_2064_, v___x_2065_, v___x_2066_, v___x_2093_);
v___x_2095_ = l_Lean_Name_toString(v___x_2094_, v___x_2067_);
v___x_2096_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_2091_, v___x_2092_, v___x_2095_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_apply_1(v_a_2097_, v___x_2098_);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = lean_io_as_task(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_2089_);
v___x_2103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2092_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
lean_ctor_set(v___x_2103_, 2, v_cancelTk_x3f_2089_);
lean_ctor_set(v___x_2103_, 3, v___x_2101_);
v___x_2104_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2103_, v___y_2069_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_dec_ref_known(v___x_2104_, 1);
v___x_2105_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_2106_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_2105_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___y_2068_);
return v___x_2106_;
}
else
{
lean_dec_ref(v___y_2068_);
return v___x_2104_;
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v___y_2068_);
v_a_2107_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2096_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2096_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v___x_2071_);
lean_dec_ref(v___x_2066_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___x_2063_);
v___x_2115_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2);
v___x_2116_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v___x_2115_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___y_2068_);
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2063_ = stack[0].m_obj;
lean_object* v___x_2064_ = stack[1].m_obj;
lean_object* v___x_2065_ = stack[2].m_obj;
lean_object* v___x_2066_ = stack[3].m_obj;
uint8_t v___x_2067_ = stack[4].m_num;
lean_object* v___y_2068_ = stack[5].m_obj;
lean_object* v___y_2069_ = stack[6].m_obj;
lean_object* v_res_2119_;
v_res_2119_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(v___x_2063_, v___x_2064_, v___x_2065_, v___x_2066_, v___x_2067_, v___y_2068_, v___y_2069_);
stack->m_obj
 = v_res_2119_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed(lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v___x_2123_, lean_object* v___x_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
uint8_t v___x_7483__boxed_2128_; lean_object* v_res_2129_; 
v___x_7483__boxed_2128_ = lean_unbox(v___x_2124_);
v_res_2129_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2123_, v___x_7483__boxed_2128_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
return v_res_2129_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(lean_object* v_x_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2134_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_2135_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_2136_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_2137_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_2138_ = ((lean_object*)(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1));
v___x_2139_ = l_Lean_Syntax_isOfKind(v_x_2130_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; lean_object* v___f_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_box(v___x_2139_);
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2142_, 0, v___x_2134_);
lean_closure_set(v___f_2142_, 1, v___x_2135_);
lean_closure_set(v___f_2142_, 2, v___x_2136_);
lean_closure_set(v___f_2142_, 3, v___x_2137_);
lean_closure_set(v___f_2142_, 4, v___x_2141_);
v___x_2143_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_2142_, v_a_2131_, v_a_2132_);
return v___x_2143_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2130_ = stack[0].m_obj;
lean_object* v_a_2131_ = stack[1].m_obj;
lean_object* v_a_2132_ = stack[2].m_obj;
lean_object* v_res_2144_;
v_res_2144_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(v_x_2130_, v_a_2131_, v_a_2132_);
stack->m_obj
 = v_res_2144_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___boxed(lean_object* v_x_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(v_x_2145_, v_a_2146_, v_a_2147_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2149_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(lean_object* v_val_2150_, lean_object* v_inst_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_2150_);
return v___x_2156_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2150_ = stack[0].m_obj;
lean_object* v_a_2152_ = stack[2].m_obj;
lean_object* v___y_2153_ = stack[3].m_obj;
lean_object* v___y_2154_ = stack[4].m_obj;
lean_object* v_res_2157_;
v_res_2157_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(v_val_2150_, lean_box(0), v_a_2152_, v___y_2153_, v___y_2154_);
stack->m_obj
 = v_res_2157_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(lean_object* v_val_2158_, lean_object* v_inst_2159_, lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(v_val_2158_, v_inst_2159_, v_a_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v_val_2158_);
return v_res_2164_;
}
}
static lean_object* _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_unsigned_to_nat(16u);
v___x_2167_ = lean_mk_array(v___x_2166_, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_obj_once(&l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_, &l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2168_);
return v___x_2170_;
}
}
lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_obj_once(&l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_, &l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
v___x_2173_ = lean_st_mk_ref(v___x_2172_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2175_;
v_res_2175_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2____boxed(lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(lean_object* v_a_2178_, lean_object* v_b_2179_, lean_object* v_x_2180_){
_start:
{
if (lean_obj_tag(v_x_2180_) == 0)
{
lean_dec(v_b_2179_);
lean_dec_ref(v_a_2178_);
return v_x_2180_;
}
else
{
lean_object* v_key_2181_; lean_object* v_value_2182_; lean_object* v_tail_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2195_; 
v_key_2181_ = lean_ctor_get(v_x_2180_, 0);
v_value_2182_ = lean_ctor_get(v_x_2180_, 1);
v_tail_2183_ = lean_ctor_get(v_x_2180_, 2);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_x_2180_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2185_ = v_x_2180_;
v_isShared_2186_ = v_isSharedCheck_2195_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_tail_2183_);
lean_inc(v_value_2182_);
lean_inc(v_key_2181_);
lean_dec(v_x_2180_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2195_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_string_dec_eq(v_key_2181_, v_a_2178_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2188_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_2178_, v_b_2179_, v_tail_2183_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 2, v___x_2188_);
v___x_2190_ = v___x_2185_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_key_2181_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_value_2182_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
else
{
lean_object* v___x_2193_; 
lean_dec(v_value_2182_);
lean_dec(v_key_2181_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v_b_2179_);
lean_ctor_set(v___x_2185_, 0, v_a_2178_);
v___x_2193_ = v___x_2185_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2178_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_b_2179_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_tail_2183_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 0)
{
return v_x_2196_;
}
else
{
lean_object* v_key_2198_; lean_object* v_value_2199_; lean_object* v_tail_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2223_; 
v_key_2198_ = lean_ctor_get(v_x_2197_, 0);
v_value_2199_ = lean_ctor_get(v_x_2197_, 1);
v_tail_2200_ = lean_ctor_get(v_x_2197_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_x_2197_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2202_ = v_x_2197_;
v_isShared_2203_ = v_isSharedCheck_2223_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_tail_2200_);
lean_inc(v_value_2199_);
lean_inc(v_key_2198_);
lean_dec(v_x_2197_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2223_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; uint64_t v___x_2205_; uint64_t v___x_2206_; uint64_t v___x_2207_; uint64_t v_fold_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2204_ = lean_array_get_size(v_x_2196_);
v___x_2205_ = lean_string_hash(v_key_2198_);
v___x_2206_ = 32ULL;
v___x_2207_ = lean_uint64_shift_right(v___x_2205_, v___x_2206_);
v_fold_2208_ = lean_uint64_xor(v___x_2205_, v___x_2207_);
v___x_2209_ = 16ULL;
v___x_2210_ = lean_uint64_shift_right(v_fold_2208_, v___x_2209_);
v___x_2211_ = lean_uint64_xor(v_fold_2208_, v___x_2210_);
v___x_2212_ = lean_uint64_to_usize(v___x_2211_);
v___x_2213_ = lean_usize_of_nat(v___x_2204_);
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_sub(v___x_2213_, v___x_2214_);
v___x_2216_ = lean_usize_land(v___x_2212_, v___x_2215_);
v___x_2217_ = lean_array_uget_borrowed(v_x_2196_, v___x_2216_);
lean_inc(v___x_2217_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 2, v___x_2217_);
v___x_2219_ = v___x_2202_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_key_2198_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_value_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_array_uset(v_x_2196_, v___x_2216_, v___x_2219_);
v_x_2196_ = v___x_2220_;
v_x_2197_ = v_tail_2200_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2224_, lean_object* v_source_2225_, lean_object* v_target_2226_){
_start:
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = lean_array_get_size(v_source_2225_);
v___x_2228_ = lean_nat_dec_lt(v_i_2224_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v_source_2225_);
lean_dec(v_i_2224_);
return v_target_2226_;
}
else
{
lean_object* v_es_2229_; lean_object* v___x_2230_; lean_object* v_source_2231_; lean_object* v_target_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_es_2229_ = lean_array_fget(v_source_2225_, v_i_2224_);
v___x_2230_ = lean_box(0);
v_source_2231_ = lean_array_fset(v_source_2225_, v_i_2224_, v___x_2230_);
v_target_2232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2226_, v_es_2229_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_add(v_i_2224_, v___x_2233_);
lean_dec(v_i_2224_);
v_i_2224_ = v___x_2234_;
v_source_2225_ = v_source_2231_;
v_target_2226_ = v_target_2232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(lean_object* v_data_2236_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_nbuckets_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2237_ = lean_array_get_size(v_data_2236_);
v___x_2238_ = lean_unsigned_to_nat(2u);
v_nbuckets_2239_ = lean_nat_mul(v___x_2237_, v___x_2238_);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_mk_array(v_nbuckets_2239_, v___x_2241_);
v___x_2243_ = lean_array_propagate_mark(v_data_2236_, v___x_2242_);
v___x_2244_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(v___x_2240_, v_data_2236_, v___x_2243_);
return v___x_2244_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(lean_object* v_a_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2246_) == 0)
{
uint8_t v___x_2247_; 
v___x_2247_ = 0;
return v___x_2247_;
}
else
{
lean_object* v_key_2248_; lean_object* v_tail_2249_; uint8_t v___x_2250_; 
v_key_2248_ = lean_ctor_get(v_x_2246_, 0);
v_tail_2249_ = lean_ctor_get(v_x_2246_, 2);
v___x_2250_ = lean_string_dec_eq(v_key_2248_, v_a_2245_);
if (v___x_2250_ == 0)
{
v_x_2246_ = v_tail_2249_;
goto _start;
}
else
{
return v___x_2250_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2245_ = stack[0].m_obj;
lean_object* v_x_2246_ = stack[1].m_obj;
uint8_t v_res_2252_;
v_res_2252_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2245_, v_x_2246_);
stack->m_num = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg___boxed(lean_object* v_a_2253_, lean_object* v_x_2254_){
_start:
{
uint8_t v_res_2255_; lean_object* v_r_2256_; 
v_res_2255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2253_, v_x_2254_);
lean_dec(v_x_2254_);
lean_dec_ref(v_a_2253_);
v_r_2256_ = lean_box(v_res_2255_);
return v_r_2256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object* v_m_2257_, lean_object* v_a_2258_, lean_object* v_b_2259_){
_start:
{
lean_object* v_size_2260_; lean_object* v_buckets_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2304_; 
v_size_2260_ = lean_ctor_get(v_m_2257_, 0);
v_buckets_2261_ = lean_ctor_get(v_m_2257_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_m_2257_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2263_ = v_m_2257_;
v_isShared_2264_ = v_isSharedCheck_2304_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_buckets_2261_);
lean_inc(v_size_2260_);
lean_dec(v_m_2257_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2304_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; uint64_t v___x_2266_; uint64_t v___x_2267_; uint64_t v___x_2268_; uint64_t v_fold_2269_; uint64_t v___x_2270_; uint64_t v___x_2271_; uint64_t v___x_2272_; size_t v___x_2273_; size_t v___x_2274_; size_t v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; lean_object* v_bkt_2278_; uint8_t v___x_2279_; 
v___x_2265_ = lean_array_get_size(v_buckets_2261_);
v___x_2266_ = lean_string_hash(v_a_2258_);
v___x_2267_ = 32ULL;
v___x_2268_ = lean_uint64_shift_right(v___x_2266_, v___x_2267_);
v_fold_2269_ = lean_uint64_xor(v___x_2266_, v___x_2268_);
v___x_2270_ = 16ULL;
v___x_2271_ = lean_uint64_shift_right(v_fold_2269_, v___x_2270_);
v___x_2272_ = lean_uint64_xor(v_fold_2269_, v___x_2271_);
v___x_2273_ = lean_uint64_to_usize(v___x_2272_);
v___x_2274_ = lean_usize_of_nat(v___x_2265_);
v___x_2275_ = ((size_t)1ULL);
v___x_2276_ = lean_usize_sub(v___x_2274_, v___x_2275_);
v___x_2277_ = lean_usize_land(v___x_2273_, v___x_2276_);
v_bkt_2278_ = lean_array_uget_borrowed(v_buckets_2261_, v___x_2277_);
v___x_2279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2258_, v_bkt_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; lean_object* v_size_x27_2281_; lean_object* v___x_2282_; lean_object* v_buckets_x27_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v_size_x27_2281_ = lean_nat_add(v_size_2260_, v___x_2280_);
lean_dec(v_size_2260_);
lean_inc(v_bkt_2278_);
v___x_2282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2258_);
lean_ctor_set(v___x_2282_, 1, v_b_2259_);
lean_ctor_set(v___x_2282_, 2, v_bkt_2278_);
v_buckets_x27_2283_ = lean_array_uset(v_buckets_2261_, v___x_2277_, v___x_2282_);
v___x_2284_ = lean_unsigned_to_nat(4u);
v___x_2285_ = lean_nat_mul(v_size_x27_2281_, v___x_2284_);
v___x_2286_ = lean_unsigned_to_nat(3u);
v___x_2287_ = lean_nat_div(v___x_2285_, v___x_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_array_get_size(v_buckets_x27_2283_);
v___x_2289_ = lean_nat_dec_le(v___x_2287_, v___x_2288_);
lean_dec(v___x_2287_);
if (v___x_2289_ == 0)
{
lean_object* v_val_2290_; lean_object* v___x_2292_; 
v_val_2290_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(v_buckets_x27_2283_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v_val_2290_);
lean_ctor_set(v___x_2263_, 0, v_size_x27_2281_);
v___x_2292_ = v___x_2263_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_size_x27_2281_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_val_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
else
{
lean_object* v___x_2295_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v_buckets_x27_2283_);
lean_ctor_set(v___x_2263_, 0, v_size_x27_2281_);
v___x_2295_ = v___x_2263_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_size_x27_2281_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_buckets_x27_2283_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_object* v___x_2297_; lean_object* v_buckets_x27_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_inc(v_bkt_2278_);
v___x_2297_ = lean_box(0);
v_buckets_x27_2298_ = lean_array_uset(v_buckets_2261_, v___x_2277_, v___x_2297_);
v___x_2299_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_2258_, v_b_2259_, v_bkt_2278_);
v___x_2300_ = lean_array_uset(v_buckets_x27_2298_, v___x_2277_, v___x_2299_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v___x_2300_);
v___x_2302_ = v___x_2263_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_size_2260_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(lean_object* v_m_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_buckets_2307_; lean_object* v___x_2308_; uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v_fold_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_buckets_2307_ = lean_ctor_get(v_m_2305_, 1);
v___x_2308_ = lean_array_get_size(v_buckets_2307_);
v___x_2309_ = lean_string_hash(v_a_2306_);
v___x_2310_ = 32ULL;
v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
v_fold_2312_ = lean_uint64_xor(v___x_2309_, v___x_2311_);
v___x_2313_ = 16ULL;
v___x_2314_ = lean_uint64_shift_right(v_fold_2312_, v___x_2313_);
v___x_2315_ = lean_uint64_xor(v_fold_2312_, v___x_2314_);
v___x_2316_ = lean_uint64_to_usize(v___x_2315_);
v___x_2317_ = lean_usize_of_nat(v___x_2308_);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_sub(v___x_2317_, v___x_2318_);
v___x_2320_ = lean_usize_land(v___x_2316_, v___x_2319_);
v___x_2321_ = lean_array_uget_borrowed(v_buckets_2307_, v___x_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2306_, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2305_ = stack[0].m_obj;
lean_object* v_a_2306_ = stack[1].m_obj;
uint8_t v_res_2323_;
v_res_2323_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_2305_, v_a_2306_);
stack->m_num = v_res_2323_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg___boxed(lean_object* v_m_2324_, lean_object* v_a_2325_){
_start:
{
uint8_t v_res_2326_; lean_object* v_r_2327_; 
v_res_2326_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_2324_, v_a_2325_);
lean_dec_ref(v_a_2325_);
lean_dec_ref(v_m_2324_);
v_r_2327_ = lean_box(v_res_2326_);
return v_r_2327_;
}
}
lean_object* l_Lean_Server_Test_Cancel_mkTestTask(lean_object* v_label_2328_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_fst_2334_; lean_object* v_snd_2335_; uint8_t v___x_2337_; 
v___x_2330_ = lean_io_promise_new();
v___x_2331_ = l_Lean_Server_Test_Cancel_testTasksRef;
v___x_2332_ = lean_st_ref_take(v___x_2331_);
v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v___x_2332_, v_label_2328_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_inc(v___x_2330_);
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2330_);
v___x_2339_ = lean_io_promise_result_opt(v___x_2330_);
lean_dec(v___x_2330_);
v___x_2340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v___x_2332_, v_label_2328_, v___x_2339_);
v_fst_2334_ = v___x_2338_;
v_snd_2335_ = v___x_2340_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2341_; 
lean_dec(v___x_2330_);
lean_dec_ref(v_label_2328_);
v___x_2341_ = lean_box(0);
v_fst_2334_ = v___x_2341_;
v_snd_2335_ = v___x_2332_;
goto v___jp_2333_;
}
v___jp_2333_:
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_st_ref_put(v___x_2331_, v_snd_2335_);
return v_fst_2334_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel_mkTestTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_2328_ = stack[0].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l_Lean_Server_Test_Cancel_mkTestTask(v_label_2328_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_mkTestTask___boxed(lean_object* v_label_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_Server_Test_Cancel_mkTestTask(v_label_2343_);
return v_res_2345_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(lean_object* v_00_u03b2_2346_, lean_object* v_m_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_2347_, v_a_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2347_ = stack[1].m_obj;
lean_object* v_a_2348_ = stack[2].m_obj;
uint8_t v_res_2350_;
v_res_2350_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(lean_box(0), v_m_2347_, v_a_2348_);
stack->m_num = v_res_2350_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___boxed(lean_object* v_00_u03b2_2351_, lean_object* v_m_2352_, lean_object* v_a_2353_){
_start:
{
uint8_t v_res_2354_; lean_object* v_r_2355_; 
v_res_2354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(v_00_u03b2_2351_, v_m_2352_, v_a_2353_);
lean_dec_ref(v_a_2353_);
lean_dec_ref(v_m_2352_);
v_r_2355_ = lean_box(v_res_2354_);
return v_r_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1(lean_object* v_00_u03b2_2356_, lean_object* v_m_2357_, lean_object* v_a_2358_, lean_object* v_b_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_m_2357_, v_a_2358_, v_b_2359_);
return v___x_2360_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(lean_object* v_00_u03b2_2361_, lean_object* v_a_2362_, lean_object* v_x_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2362_, v_x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2362_ = stack[1].m_obj;
lean_object* v_x_2363_ = stack[2].m_obj;
uint8_t v_res_2365_;
v_res_2365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(lean_box(0), v_a_2362_, v_x_2363_);
stack->m_num = v_res_2365_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2366_, lean_object* v_a_2367_, lean_object* v_x_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(v_00_u03b2_2366_, v_a_2367_, v_x_2368_);
lean_dec(v_x_2368_);
lean_dec_ref(v_a_2367_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2(lean_object* v_00_u03b2_2371_, lean_object* v_data_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(v_data_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3(lean_object* v_00_u03b2_2374_, lean_object* v_a_2375_, lean_object* v_b_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_2375_, v_b_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2379_, lean_object* v_i_2380_, lean_object* v_source_2381_, lean_object* v_target_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(v_i_2380_, v_source_2381_, v_target_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2385_, v_x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(lean_object* v_a_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_box(0);
return v___x_2415_;
}
else
{
lean_object* v_key_2416_; lean_object* v_value_2417_; lean_object* v_tail_2418_; uint8_t v___x_2419_; 
v_key_2416_ = lean_ctor_get(v_x_2414_, 0);
v_value_2417_ = lean_ctor_get(v_x_2414_, 1);
v_tail_2418_ = lean_ctor_get(v_x_2414_, 2);
v___x_2419_ = lean_string_dec_eq(v_key_2416_, v_a_2413_);
if (v___x_2419_ == 0)
{
v_x_2414_ = v_tail_2418_;
goto _start;
}
else
{
lean_object* v___x_2421_; 
lean_inc(v_value_2417_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_value_2417_);
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg___boxed(lean_object* v_a_2422_, lean_object* v_x_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_2422_, v_x_2423_);
lean_dec(v_x_2423_);
lean_dec_ref(v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object* v_m_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_buckets_2427_; lean_object* v___x_2428_; uint64_t v___x_2429_; uint64_t v___x_2430_; uint64_t v___x_2431_; uint64_t v_fold_2432_; uint64_t v___x_2433_; uint64_t v___x_2434_; uint64_t v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_buckets_2427_ = lean_ctor_get(v_m_2425_, 1);
v___x_2428_ = lean_array_get_size(v_buckets_2427_);
v___x_2429_ = lean_string_hash(v_a_2426_);
v___x_2430_ = 32ULL;
v___x_2431_ = lean_uint64_shift_right(v___x_2429_, v___x_2430_);
v_fold_2432_ = lean_uint64_xor(v___x_2429_, v___x_2431_);
v___x_2433_ = 16ULL;
v___x_2434_ = lean_uint64_shift_right(v_fold_2432_, v___x_2433_);
v___x_2435_ = lean_uint64_xor(v_fold_2432_, v___x_2434_);
v___x_2436_ = lean_uint64_to_usize(v___x_2435_);
v___x_2437_ = lean_usize_of_nat(v___x_2428_);
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_sub(v___x_2437_, v___x_2438_);
v___x_2440_ = lean_usize_land(v___x_2436_, v___x_2439_);
v___x_2441_ = lean_array_uget_borrowed(v_buckets_2427_, v___x_2440_);
v___x_2442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_2426_, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg___boxed(lean_object* v_m_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_m_2443_, v_a_2444_);
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_m_2443_);
return v_res_2445_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(lean_object* v_x_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1));
lean_inc(v_x_2449_);
v___x_2453_ = l_Lean_Syntax_isOfKind(v_x_2449_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec(v_x_2449_);
v___x_2454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; lean_object* v_label_2456_; lean_object* v_label_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2455_ = lean_unsigned_to_nat(1u);
v_label_2456_ = l_Lean_Syntax_getArg(v_x_2449_, v___x_2455_);
lean_dec(v_x_2449_);
v_label_2457_ = l_Lean_TSyntax_getString(v_label_2456_);
lean_dec(v_label_2456_);
v___x_2458_ = l_Lean_Server_Test_Cancel_testTasksRef;
v___x_2459_ = lean_st_ref_get(v___x_2458_);
v___x_2460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_2459_, v_label_2457_);
lean_dec(v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_ref_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_ref_2461_ = lean_ctor_get(v_a_2450_, 2);
v___x_2462_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0));
v___x_2463_ = lean_string_append(v___x_2462_, v_label_2457_);
lean_dec_ref(v_label_2457_);
v___x_2464_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2463_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2484_; 
v_a_2473_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2475_ = v___x_2464_;
v_isShared_2476_ = v_isSharedCheck_2484_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2464_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2484_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2477_ = lean_io_error_to_string(v_a_2473_);
v___x_2478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
v___x_2479_ = l_Lean_MessageData_ofFormat(v___x_2478_);
lean_inc(v_ref_2461_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_ref_2461_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2480_);
v___x_2482_ = v___x_2475_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_val_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2527_; 
v_val_2485_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2487_ = v___x_2460_;
v_isShared_2488_ = v_isSharedCheck_2527_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_val_2485_);
lean_dec(v___x_2460_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2527_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_io_wait(v_val_2485_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_ref_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_ref_2490_ = lean_ctor_get(v_a_2450_, 2);
v___x_2491_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1));
v___x_2492_ = lean_string_append(v___x_2491_, v_label_2457_);
lean_dec_ref(v_label_2457_);
v___x_2493_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2));
v___x_2494_ = lean_string_append(v___x_2492_, v___x_2493_);
v___x_2495_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2494_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_del_object(v___x_2487_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2517_; 
v_a_2504_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2506_ = v___x_2495_;
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2495_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = lean_io_error_to_string(v_a_2504_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 3);
lean_ctor_set(v___x_2487_, 0, v___x_2508_);
v___x_2510_ = v___x_2487_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2511_ = l_Lean_MessageData_ofFormat(v___x_2510_);
lean_inc(v_ref_2490_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_ref_2490_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2512_);
v___x_2514_ = v___x_2506_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
else
{
lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2487_);
lean_dec_ref(v_label_2457_);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2489_, 0);
lean_dec(v_unused_2526_);
v___x_2519_ = v___x_2489_;
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
else
{
lean_dec(v___x_2489_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_box(0);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2449_ = stack[0].m_obj;
lean_object* v_a_2450_ = stack[1].m_obj;
lean_object* v_res_2528_;
v_res_2528_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_2449_, v_a_2450_);
stack->m_obj
 = v_res_2528_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___boxed(lean_object* v_x_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_2529_, v_a_2530_);
lean_dec_ref(v_a_2530_);
return v_res_2532_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(lean_object* v_x_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_2533_, v_a_2540_);
return v___x_2543_;
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2533_ = stack[0].m_obj;
lean_object* v_a_2534_ = stack[1].m_obj;
lean_object* v_a_2535_ = stack[2].m_obj;
lean_object* v_a_2536_ = stack[3].m_obj;
lean_object* v_a_2537_ = stack[4].m_obj;
lean_object* v_a_2538_ = stack[5].m_obj;
lean_object* v_a_2539_ = stack[6].m_obj;
lean_object* v_a_2540_ = stack[7].m_obj;
lean_object* v_a_2541_ = stack[8].m_obj;
lean_object* v_res_2544_;
v_res_2544_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(v_x_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
stack->m_obj
 = v_res_2544_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___boxed(lean_object* v_x_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(v_x_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(lean_object* v_00_u03b2_2556_, lean_object* v_m_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_m_2557_, v_a_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___boxed(lean_object* v_00_u03b2_2560_, lean_object* v_m_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(v_00_u03b2_2560_, v_m_2561_, v_a_2562_);
lean_dec_ref(v_a_2562_);
lean_dec_ref(v_m_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(lean_object* v_00_u03b2_2564_, lean_object* v_a_2565_, lean_object* v_x_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_2565_, v_x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2568_, lean_object* v_a_2569_, lean_object* v_x_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(v_00_u03b2_2568_, v_a_2569_, v_x_2570_);
lean_dec(v_x_2570_);
lean_dec_ref(v_a_2569_);
return v_res_2571_;
}
}
lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_, &l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
v___x_2574_ = lean_st_mk_ref(v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2576_;
v_res_2576_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2576_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2____boxed(lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
return v_res_2578_;
}
}
lean_object* l_Lean_Server_Test_Cancel_getSyncPromise(lean_object* v_label_2579_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; 
v___x_2581_ = lean_io_promise_new();
v___x_2582_ = l_Lean_Server_Test_Cancel_syncPromisesRef;
v___x_2583_ = lean_st_ref_take(v___x_2582_);
v___x_2588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_2583_, v_label_2579_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; 
lean_inc(v___x_2581_);
v___x_2589_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v___x_2583_, v_label_2579_, v___x_2581_);
v_fst_2585_ = v___x_2581_;
v_snd_2586_ = v___x_2589_;
goto v___jp_2584_;
}
else
{
lean_object* v_val_2590_; 
lean_dec(v___x_2581_);
lean_dec_ref(v_label_2579_);
v_val_2590_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v___x_2588_, 1);
v_fst_2585_ = v_val_2590_;
v_snd_2586_ = v___x_2583_;
goto v___jp_2584_;
}
v___jp_2584_:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_st_ref_put(v___x_2582_, v_snd_2586_);
return v_fst_2585_;
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel_getSyncPromise_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_2579_ = stack[0].m_obj;
lean_object* v_res_2591_;
v_res_2591_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_2579_);
stack->m_obj
 = v_res_2591_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_getSyncPromise___boxed(lean_object* v_label_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_2592_);
return v_res_2594_;
}
}
lean_object* l_Lean_Server_Test_Cancel_resolveSyncPromise(lean_object* v_label_2595_){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_2595_);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_io_promise_resolve(v___x_2598_, v___x_2597_);
lean_dec(v___x_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel_resolveSyncPromise_0interp(lean_interpreter_value* stack)
{
lean_object* v_label_2595_ = stack[0].m_obj;
lean_object* v_res_2600_;
v_res_2600_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_label_2595_);
stack->m_obj
 = v_res_2600_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_resolveSyncPromise___boxed(lean_object* v_label_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_label_2601_);
return v_res_2603_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(lean_object* v_x_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1));
lean_inc(v_x_2625_);
v___x_2629_ = l_Lean_Syntax_isOfKind(v_x_2625_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; 
lean_dec(v_x_2625_);
v___x_2630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_2630_;
}
else
{
lean_object* v___x_2631_; lean_object* v_label_2632_; lean_object* v_lbl_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2631_ = lean_unsigned_to_nat(1u);
v_label_2632_ = l_Lean_Syntax_getArg(v_x_2625_, v___x_2631_);
lean_dec(v_x_2625_);
v_lbl_2633_ = l_Lean_TSyntax_getString(v_label_2632_);
lean_dec(v_label_2632_);
lean_inc_ref(v_lbl_2633_);
v___x_2634_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_lbl_2633_);
v___x_2635_ = lean_io_promise_result_opt(v___x_2634_);
lean_dec(v___x_2634_);
v___x_2636_ = lean_io_wait(v___x_2635_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_ref_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_ref_2637_ = lean_ctor_get(v_a_2626_, 2);
v___x_2638_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0));
v___x_2639_ = lean_string_append(v___x_2638_, v_lbl_2633_);
lean_dec_ref(v_lbl_2633_);
v___x_2640_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
v___x_2642_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2662_; 
v_a_2651_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2653_ = v___x_2642_;
v_isShared_2654_ = v_isSharedCheck_2662_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2642_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2662_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2655_ = lean_io_error_to_string(v_a_2651_);
v___x_2656_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
v___x_2657_ = l_Lean_MessageData_ofFormat(v___x_2656_);
lean_inc(v_ref_2637_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_ref_2637_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2658_);
v___x_2660_ = v___x_2653_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v_lbl_2633_);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2636_, 0);
lean_dec(v_unused_2671_);
v___x_2664_ = v___x_2636_;
v_isShared_2665_ = v_isSharedCheck_2670_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v___x_2636_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2670_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2666_ = lean_box(0);
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2666_);
v___x_2668_ = v___x_2664_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
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
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2625_ = stack[0].m_obj;
lean_object* v_a_2626_ = stack[1].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_2625_, v_a_2626_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___boxed(lean_object* v_x_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_2673_, v_a_2674_);
lean_dec_ref(v_a_2674_);
return v_res_2676_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(lean_object* v_x_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_2677_, v_a_2684_);
return v___x_2687_;
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2677_ = stack[0].m_obj;
lean_object* v_a_2678_ = stack[1].m_obj;
lean_object* v_a_2679_ = stack[2].m_obj;
lean_object* v_a_2680_ = stack[3].m_obj;
lean_object* v_a_2681_ = stack[4].m_obj;
lean_object* v_a_2682_ = stack[5].m_obj;
lean_object* v_a_2683_ = stack[6].m_obj;
lean_object* v_a_2684_ = stack[7].m_obj;
lean_object* v_a_2685_ = stack[8].m_obj;
lean_object* v_res_2688_;
v_res_2688_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(v_x_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
stack->m_obj
 = v_res_2688_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___boxed(lean_object* v_x_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(v_x_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
return v_res_2699_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(lean_object* v___x_2720_, lean_object* v_val_2721_, lean_object* v_a_x3f_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_io_promise_resolve(v___x_2720_, v_val_2721_);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2720_ = stack[0].m_obj;
lean_object* v_val_2721_ = stack[1].m_obj;
lean_object* v_a_x3f_2722_ = stack[2].m_obj;
lean_object* v_res_2726_;
v_res_2726_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2720_, v_val_2721_, v_a_x3f_2722_);
stack->m_obj
 = v_res_2726_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0___boxed(lean_object* v___x_2727_, lean_object* v_val_2728_, lean_object* v_a_x3f_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2727_, v_val_2728_, v_a_x3f_2729_);
lean_dec(v_a_x3f_2729_);
lean_dec(v_val_2728_);
return v_res_2731_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(lean_object* v___y_2732_){
_start:
{
lean_object* v_toCold_2738_; lean_object* v_cancelTk_x3f_2739_; 
v_toCold_2738_ = lean_ctor_get(v___y_2732_, 0);
v_cancelTk_x3f_2739_ = lean_ctor_get(v_toCold_2738_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2739_) == 1)
{
lean_object* v_val_2740_; uint8_t v___x_2741_; 
v_val_2740_ = lean_ctor_get(v_cancelTk_x3f_2739_, 0);
v___x_2741_ = l_IO_CancelToken_isSet(v_val_2740_);
if (v___x_2741_ == 0)
{
goto v___jp_2734_;
}
else
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_dec_ref_known(v___x_2742_, 1);
goto v___jp_2734_;
}
else
{
return v___x_2742_;
}
}
}
else
{
goto v___jp_2734_;
}
v___jp_2734_:
{
uint32_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = 10;
v___x_2736_ = l_IO_sleep(v___x_2735_);
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2732_ = stack[0].m_obj;
lean_object* v_res_2743_;
v_res_2743_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_2732_);
stack->m_obj
 = v_res_2743_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg___boxed(lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_2744_);
lean_dec_ref(v___y_2744_);
return v_res_2746_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2748_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_2749_ = lean_unsigned_to_nat(50u);
v___x_2750_ = lean_unsigned_to_nat(302u);
v___x_2751_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0));
v___x_2752_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_2753_ = l_mkPanicMessageWithDecl(v___x_2752_, v___x_2751_, v___x_2750_, v___x_2749_, v___x_2748_);
return v___x_2753_;
}
}
lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(lean_object* v_x_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1));
lean_inc(v_x_2755_);
v___x_2766_ = l_Lean_Syntax_isOfKind(v_x_2755_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
lean_dec(v_x_2755_);
v___x_2767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v_label_2769_; lean_object* v_lbl_2770_; lean_object* v___x_2771_; 
v___x_2768_ = lean_unsigned_to_nat(1u);
v_label_2769_ = l_Lean_Syntax_getArg(v_x_2755_, v___x_2768_);
lean_dec(v_x_2755_);
v_lbl_2770_ = l_Lean_TSyntax_getString(v_label_2769_);
lean_dec(v_label_2769_);
lean_inc_ref(v_lbl_2770_);
v___x_2771_ = l_Lean_Server_Test_Cancel_mkTestTask(v_lbl_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = l_Lean_Server_Test_Cancel_testTasksRef;
v___x_2773_ = lean_st_ref_get(v___x_2772_);
v___x_2774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_2773_, v_lbl_2770_);
lean_dec_ref(v_lbl_2770_);
lean_dec(v___x_2773_);
if (lean_obj_tag(v___x_2774_) == 1)
{
lean_object* v_val_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2784_; 
v_val_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_val_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_io_wait(v_val_2775_);
lean_dec(v___x_2780_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2779_);
v___x_2782_ = v___x_2777_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2779_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v___x_2774_);
v___x_2785_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1);
v___x_2786_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_2785_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
return v___x_2786_;
}
}
else
{
lean_object* v_val_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2836_; 
v_val_2787_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2789_ = v___x_2771_;
v_isShared_2790_ = v_isSharedCheck_2836_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_val_2787_);
lean_dec(v___x_2771_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2836_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_ref_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_ref_2791_ = lean_ctor_get(v_a_2762_, 2);
v___x_2792_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2));
lean_inc_ref(v_lbl_2770_);
v___x_2793_ = lean_string_append(v_lbl_2770_, v___x_2792_);
v___x_2794_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_a_2798_; lean_object* v___x_2811_; 
lean_dec_ref_known(v___x_2794_, 1);
v___x_2795_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_lbl_2770_);
v___x_2796_ = lean_box(0);
v___x_2811_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v_a_2762_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_dec_ref_known(v___x_2811_, 1);
v_a_2798_ = v___x_2796_;
goto v___jp_2797_;
}
else
{
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_a_2798_ = v_a_2812_;
goto v___jp_2797_;
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2789_);
v_a_2813_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2814_ = lean_box(0);
v___x_2815_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2796_, v_val_2787_, v___x_2814_);
lean_dec(v_val_2787_);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; 
v_unused_2823_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2823_);
v___x_2817_ = v___x_2815_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v___x_2815_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 1);
lean_ctor_set(v___x_2817_, 0, v_a_2813_);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2813_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
v___jp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v_a_2798_);
v___x_2800_ = v___x_2789_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2798_);
v___x_2800_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v___x_2801_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2796_, v_val_2787_, v___x_2800_);
lean_dec_ref(v___x_2800_);
lean_dec(v_val_2787_);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v___x_2801_, 0);
lean_dec(v_unused_2809_);
v___x_2803_ = v___x_2801_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_dec(v___x_2801_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v_a_2798_);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2798_);
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
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2789_);
lean_dec(v_val_2787_);
lean_dec_ref(v_lbl_2770_);
v_a_2824_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2826_ = v___x_2794_;
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2794_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2828_ = lean_io_error_to_string(v_a_2824_);
v___x_2829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
v___x_2830_ = l_Lean_MessageData_ofFormat(v___x_2829_);
lean_inc(v_ref_2791_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_ref_2791_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2831_);
v___x_2833_ = v___x_2826_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2755_ = stack[0].m_obj;
lean_object* v_a_2756_ = stack[1].m_obj;
lean_object* v_a_2757_ = stack[2].m_obj;
lean_object* v_a_2758_ = stack[3].m_obj;
lean_object* v_a_2759_ = stack[4].m_obj;
lean_object* v_a_2760_ = stack[5].m_obj;
lean_object* v_a_2761_ = stack[6].m_obj;
lean_object* v_a_2762_ = stack[7].m_obj;
lean_object* v_a_2763_ = stack[8].m_obj;
lean_object* v_res_2837_;
v_res_2837_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(v_x_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
stack->m_obj
 = v_res_2837_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___boxed(lean_object* v_x_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(v_x_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
return v_res_2848_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(lean_object* v_inst_2849_, lean_object* v_a_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_2857_);
return v___x_2860_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2850_ = stack[1].m_obj;
lean_object* v___y_2851_ = stack[2].m_obj;
lean_object* v___y_2852_ = stack[3].m_obj;
lean_object* v___y_2853_ = stack[4].m_obj;
lean_object* v___y_2854_ = stack[5].m_obj;
lean_object* v___y_2855_ = stack[6].m_obj;
lean_object* v___y_2856_ = stack[7].m_obj;
lean_object* v___y_2857_ = stack[8].m_obj;
lean_object* v___y_2858_ = stack[9].m_obj;
lean_object* v_res_2861_;
v_res_2861_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(lean_box(0), v_a_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
stack->m_obj
 = v_res_2861_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___boxed(lean_object* v_inst_2862_, lean_object* v_a_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(v_inst_2862_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2873_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Test_Cancel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_unblockedCancelTkRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_unblockedCancelTkRef);
lean_dec_ref(res);
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_cmdOnceRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_cmdOnceRef);
lean_dec_ref(res);
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_testTasksRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_testTasksRef);
lean_dec_ref(res);
res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_Test_Cancel_syncPromisesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_Test_Cancel_syncPromisesRef);
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
