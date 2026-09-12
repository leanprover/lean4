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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
lean_object* v___f_86_; lean_object* v___x_9706__overap_87_; lean_object* v___x_88_; 
v___f_86_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0));
v___x_9706__overap_87_ = lean_panic_fn_borrowed(v___f_86_, v_msg_76_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
lean_inc_ref(v___y_77_);
v___x_88_ = lean_apply_9(v___x_9706__overap_87_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(lean_object* v_val_100_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_box(0);
v___x_103_ = l_IO_CancelToken_isSet(v_val_100_);
if (v___x_103_ == 0)
{
uint32_t v___x_104_; lean_object* v___x_105_; 
v___x_104_ = 30;
v___x_105_ = l_IO_sleep(v___x_104_);
goto _start;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_102_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg___boxed(lean_object* v_val_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_108_);
lean_dec_ref(v_val_108_);
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
lean_object* v___x_133_; lean_object* v_env_134_; lean_object* v___x_135_; lean_object* v_toCold_136_; lean_object* v_mctx_137_; lean_object* v_lctx_138_; lean_object* v_options_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_133_ = lean_st_ref_get(v___y_131_);
v_env_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_133_);
v___x_135_ = lean_st_ref_get(v___y_129_);
v_toCold_136_ = lean_ctor_get(v___y_130_, 0);
v_mctx_137_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_mctx_137_);
lean_dec(v___x_135_);
v_lctx_138_ = lean_ctor_get(v___y_128_, 2);
v_options_139_ = lean_ctor_get(v_toCold_136_, 2);
lean_inc_ref(v_options_139_);
lean_inc_ref(v_lctx_138_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_134_);
lean_ctor_set(v___x_140_, 1, v_mctx_137_);
lean_ctor_set(v___x_140_, 2, v_lctx_138_);
lean_ctor_set(v___x_140_, 3, v_options_139_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_127_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v_msgData_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(lean_object* v_opts_150_, lean_object* v_opt_151_){
_start:
{
lean_object* v_name_152_; lean_object* v_defValue_153_; lean_object* v_map_154_; lean_object* v___x_155_; 
v_name_152_ = lean_ctor_get(v_opt_151_, 0);
v_defValue_153_ = lean_ctor_get(v_opt_151_, 1);
v_map_154_ = lean_ctor_get(v_opts_150_, 0);
v___x_155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_154_, v_name_152_);
if (lean_obj_tag(v___x_155_) == 0)
{
uint8_t v___x_156_; 
v___x_156_ = lean_unbox(v_defValue_153_);
return v___x_156_;
}
else
{
lean_object* v_val_157_; 
v_val_157_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v___x_155_, 1);
if (lean_obj_tag(v_val_157_) == 1)
{
uint8_t v_v_158_; 
v_v_158_ = lean_ctor_get_uint8(v_val_157_, 0);
lean_dec_ref_known(v_val_157_, 0);
return v_v_158_;
}
else
{
uint8_t v___x_159_; 
lean_dec(v_val_157_);
v___x_159_ = lean_unbox(v_defValue_153_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5___boxed(lean_object* v_opts_160_, lean_object* v_opt_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_opts_160_, v_opt_161_);
lean_dec_ref(v_opt_161_);
lean_dec_ref(v_opts_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_172_, uint8_t v___y_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 1)
{
lean_object* v_pre_175_; 
v_pre_175_ = lean_ctor_get(v_x_174_, 0);
switch(lean_obj_tag(v_pre_175_))
{
case 1:
{
lean_object* v_pre_176_; 
v_pre_176_ = lean_ctor_get(v_pre_175_, 0);
switch(lean_obj_tag(v_pre_176_))
{
case 0:
{
lean_object* v_str_177_; lean_object* v_str_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_str_177_ = lean_ctor_get(v_x_174_, 1);
v_str_178_ = lean_ctor_get(v_pre_175_, 1);
v___x_179_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_180_ = lean_string_dec_eq(v_str_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_182_ = lean_string_dec_eq(v_str_178_, v___x_181_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_184_ = lean_string_dec_eq(v_str_177_, v___x_183_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
return v_suppressElabErrors_172_;
}
}
}
else
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_186_ = lean_string_dec_eq(v_str_177_, v___x_185_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
return v_suppressElabErrors_172_;
}
}
}
case 1:
{
lean_object* v_pre_187_; 
v_pre_187_ = lean_ctor_get(v_pre_176_, 0);
if (lean_obj_tag(v_pre_187_) == 0)
{
lean_object* v_str_188_; lean_object* v_str_189_; lean_object* v_str_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_str_188_ = lean_ctor_get(v_x_174_, 1);
v_str_189_ = lean_ctor_get(v_pre_175_, 1);
v_str_190_ = lean_ctor_get(v_pre_176_, 1);
v___x_191_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_192_ = lean_string_dec_eq(v_str_190_, v___x_191_);
if (v___x_192_ == 0)
{
return v___x_192_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_194_ = lean_string_dec_eq(v_str_189_, v___x_193_);
if (v___x_194_ == 0)
{
return v___x_194_;
}
else
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_196_ = lean_string_dec_eq(v_str_188_, v___x_195_);
if (v___x_196_ == 0)
{
return v___x_196_;
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
return v___y_173_;
}
}
default: 
{
return v___y_173_;
}
}
}
case 0:
{
lean_object* v_str_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_str_197_ = lean_ctor_get(v_x_174_, 1);
v___x_198_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_199_ = lean_string_dec_eq(v_str_197_, v___x_198_);
if (v___x_199_ == 0)
{
return v___x_199_;
}
else
{
return v_suppressElabErrors_172_;
}
}
default: 
{
return v___y_173_;
}
}
}
else
{
return v___y_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_200_, lean_object* v___y_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_suppressElabErrors_boxed_203_; uint8_t v___y_14291__boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_suppressElabErrors_boxed_203_ = lean_unbox(v_suppressElabErrors_200_);
v___y_14291__boxed_204_ = lean_unbox(v___y_201_);
v_res_205_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_203_, v___y_14291__boxed_204_, v_x_202_);
lean_dec(v_x_202_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(lean_object* v_ref_208_, lean_object* v_msgData_209_, uint8_t v_severity_210_, uint8_t v_isSilent_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v_currNamespace_225_; lean_object* v_openDecls_226_; lean_object* v___y_227_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; uint8_t v___y_258_; lean_object* v___y_259_; uint8_t v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; uint8_t v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; uint8_t v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; uint8_t v___x_306_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; uint8_t v___y_313_; lean_object* v___y_314_; uint8_t v___y_315_; uint8_t v___y_316_; uint8_t v___y_318_; uint8_t v___x_336_; 
v___x_306_ = 2;
v___x_336_ = l_Lean_instBEqMessageSeverity_beq(v_severity_210_, v___x_306_);
if (v___x_336_ == 0)
{
v___y_318_ = v___x_336_;
goto v___jp_317_;
}
else
{
uint8_t v___x_337_; 
lean_inc_ref(v_msgData_209_);
v___x_337_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_209_);
v___y_318_ = v___x_337_;
goto v___jp_317_;
}
v___jp_217_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v_nextMacroScope_233_; lean_object* v_ngen_234_; lean_object* v_auxDeclNGen_235_; lean_object* v_traceState_236_; lean_object* v_cache_237_; lean_object* v_messages_238_; lean_object* v_infoState_239_; lean_object* v_snapshotTasks_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_251_; 
lean_inc(v_openDecls_226_);
lean_inc(v_currNamespace_225_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_currNamespace_225_);
lean_ctor_set(v___x_228_, 1, v_openDecls_226_);
v___x_229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___y_222_);
lean_inc_ref(v___y_220_);
lean_inc_ref(v___y_224_);
v___x_230_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_230_, 0, v___y_224_);
lean_ctor_set(v___x_230_, 1, v___y_221_);
lean_ctor_set(v___x_230_, 2, v___y_223_);
lean_ctor_set(v___x_230_, 3, v___y_220_);
lean_ctor_set(v___x_230_, 4, v___x_229_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*5, v___y_218_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*5 + 1, v___y_219_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*5 + 2, v_isSilent_211_);
v___x_231_ = lean_st_ref_take(v___y_227_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
v_nextMacroScope_233_ = lean_ctor_get(v___x_231_, 1);
v_ngen_234_ = lean_ctor_get(v___x_231_, 2);
v_auxDeclNGen_235_ = lean_ctor_get(v___x_231_, 3);
v_traceState_236_ = lean_ctor_get(v___x_231_, 4);
v_cache_237_ = lean_ctor_get(v___x_231_, 5);
v_messages_238_ = lean_ctor_get(v___x_231_, 6);
v_infoState_239_ = lean_ctor_get(v___x_231_, 7);
v_snapshotTasks_240_ = lean_ctor_get(v___x_231_, 8);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_251_ == 0)
{
v___x_242_ = v___x_231_;
v_isShared_243_ = v_isSharedCheck_251_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_snapshotTasks_240_);
lean_inc(v_infoState_239_);
lean_inc(v_messages_238_);
lean_inc(v_cache_237_);
lean_inc(v_traceState_236_);
lean_inc(v_auxDeclNGen_235_);
lean_inc(v_ngen_234_);
lean_inc(v_nextMacroScope_233_);
lean_inc(v_env_232_);
lean_dec(v___x_231_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_251_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_244_ = lean_box(0);
v___x_245_ = l_Lean_MessageLog_add(v___x_230_, v_messages_238_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 6, v___x_245_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_env_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_nextMacroScope_233_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_ngen_234_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_auxDeclNGen_235_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_traceState_236_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_cache_237_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_infoState_239_);
lean_ctor_set(v_reuseFailAlloc_250_, 8, v_snapshotTasks_240_);
v___x_247_ = v_reuseFailAlloc_250_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_st_ref_put(v___y_227_, v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_244_);
return v___x_249_;
}
}
}
v___jp_252_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_278_; 
v___x_263_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_209_);
v___x_264_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_263_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_278_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_278_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_278_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_inc_ref_n(v___y_257_, 2);
v___x_269_ = l_Lean_FileMap_toPosition(v___y_257_, v___y_259_);
lean_dec(v___y_259_);
v___x_270_ = l_Lean_FileMap_toPosition(v___y_257_, v___y_262_);
lean_dec(v___y_262_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_260_ == 0)
{
lean_del_object(v___x_267_);
lean_dec_ref(v___y_255_);
v___y_218_ = v___y_256_;
v___y_219_ = v___y_258_;
v___y_220_ = v___x_272_;
v___y_221_ = v___x_269_;
v___y_222_ = v_a_265_;
v___y_223_ = v___x_271_;
v___y_224_ = v___y_261_;
v_currNamespace_225_ = v___y_254_;
v_openDecls_226_ = v___y_253_;
v___y_227_ = v___y_215_;
goto v___jp_217_;
}
else
{
uint8_t v___x_273_; 
lean_inc(v_a_265_);
v___x_273_ = l_Lean_MessageData_hasTag(v___y_255_, v_a_265_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec_ref_known(v___x_271_, 1);
lean_dec_ref(v___x_269_);
lean_dec(v_a_265_);
v___x_274_ = lean_box(0);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_274_);
v___x_276_ = v___x_267_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_del_object(v___x_267_);
v___y_218_ = v___y_256_;
v___y_219_ = v___y_258_;
v___y_220_ = v___x_272_;
v___y_221_ = v___x_269_;
v___y_222_ = v_a_265_;
v___y_223_ = v___x_271_;
v___y_224_ = v___y_261_;
v_currNamespace_225_ = v___y_254_;
v_openDecls_226_ = v___y_253_;
v___y_227_ = v___y_215_;
goto v___jp_217_;
}
}
}
}
v___jp_279_:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Syntax_getTailPos_x3f(v___y_287_, v___y_283_);
lean_dec(v___y_287_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_inc(v___y_289_);
v___y_253_ = v___y_280_;
v___y_254_ = v___y_281_;
v___y_255_ = v___y_282_;
v___y_256_ = v___y_283_;
v___y_257_ = v___y_284_;
v___y_258_ = v___y_285_;
v___y_259_ = v___y_289_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_288_;
v___y_262_ = v___y_289_;
goto v___jp_252_;
}
else
{
lean_object* v_val_291_; 
v_val_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_290_, 1);
v___y_253_ = v___y_280_;
v___y_254_ = v___y_281_;
v___y_255_ = v___y_282_;
v___y_256_ = v___y_283_;
v___y_257_ = v___y_284_;
v___y_258_ = v___y_285_;
v___y_259_ = v___y_289_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_288_;
v___y_262_ = v_val_291_;
goto v___jp_252_;
}
}
v___jp_292_:
{
lean_object* v_ref_302_; lean_object* v___x_303_; 
v_ref_302_ = l_Lean_replaceRef(v_ref_208_, v___y_298_);
v___x_303_ = l_Lean_Syntax_getPos_x3f(v_ref_302_, v___y_296_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___y_280_ = v___y_293_;
v___y_281_ = v___y_294_;
v___y_282_ = v___y_295_;
v___y_283_ = v___y_296_;
v___y_284_ = v___y_297_;
v___y_285_ = v___y_301_;
v___y_286_ = v___y_299_;
v___y_287_ = v_ref_302_;
v___y_288_ = v___y_300_;
v___y_289_ = v___x_304_;
goto v___jp_279_;
}
else
{
lean_object* v_val_305_; 
v_val_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_303_, 1);
v___y_280_ = v___y_293_;
v___y_281_ = v___y_294_;
v___y_282_ = v___y_295_;
v___y_283_ = v___y_296_;
v___y_284_ = v___y_297_;
v___y_285_ = v___y_301_;
v___y_286_ = v___y_299_;
v___y_287_ = v_ref_302_;
v___y_288_ = v___y_300_;
v___y_289_ = v_val_305_;
goto v___jp_279_;
}
}
v___jp_307_:
{
if (v___y_316_ == 0)
{
v___y_293_ = v___y_309_;
v___y_294_ = v___y_310_;
v___y_295_ = v___y_311_;
v___y_296_ = v___y_313_;
v___y_297_ = v___y_308_;
v___y_298_ = v___y_314_;
v___y_299_ = v___y_315_;
v___y_300_ = v___y_312_;
v___y_301_ = v_severity_210_;
goto v___jp_292_;
}
else
{
v___y_293_ = v___y_309_;
v___y_294_ = v___y_310_;
v___y_295_ = v___y_311_;
v___y_296_ = v___y_313_;
v___y_297_ = v___y_308_;
v___y_298_ = v___y_314_;
v___y_299_ = v___y_315_;
v___y_300_ = v___y_312_;
v___y_301_ = v___x_306_;
goto v___jp_292_;
}
}
v___jp_317_:
{
if (v___y_318_ == 0)
{
lean_object* v_toCold_319_; lean_object* v_ref_320_; uint8_t v_suppressElabErrors_321_; lean_object* v_fileName_322_; lean_object* v_fileMap_323_; lean_object* v_options_324_; lean_object* v_currNamespace_325_; lean_object* v_openDecls_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___f_329_; uint8_t v___x_330_; uint8_t v___x_331_; 
v_toCold_319_ = lean_ctor_get(v___y_214_, 0);
v_ref_320_ = lean_ctor_get(v___y_214_, 2);
v_suppressElabErrors_321_ = lean_ctor_get_uint8(v___y_214_, sizeof(void*)*3 + 1);
v_fileName_322_ = lean_ctor_get(v_toCold_319_, 0);
v_fileMap_323_ = lean_ctor_get(v_toCold_319_, 1);
v_options_324_ = lean_ctor_get(v_toCold_319_, 2);
v_currNamespace_325_ = lean_ctor_get(v_toCold_319_, 4);
v_openDecls_326_ = lean_ctor_get(v_toCold_319_, 5);
v___x_327_ = lean_box(v_suppressElabErrors_321_);
v___x_328_ = lean_box(v___y_318_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_329_, 0, v___x_327_);
lean_closure_set(v___f_329_, 1, v___x_328_);
v___x_330_ = 1;
v___x_331_ = l_Lean_instBEqMessageSeverity_beq(v_severity_210_, v___x_330_);
if (v___x_331_ == 0)
{
v___y_308_ = v_fileMap_323_;
v___y_309_ = v_openDecls_326_;
v___y_310_ = v_currNamespace_325_;
v___y_311_ = v___f_329_;
v___y_312_ = v_fileName_322_;
v___y_313_ = v___y_318_;
v___y_314_ = v_ref_320_;
v___y_315_ = v_suppressElabErrors_321_;
v___y_316_ = v___x_331_;
goto v___jp_307_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = l_Lean_warningAsError;
v___x_333_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_324_, v___x_332_);
v___y_308_ = v_fileMap_323_;
v___y_309_ = v_openDecls_326_;
v___y_310_ = v_currNamespace_325_;
v___y_311_ = v___f_329_;
v___y_312_ = v_fileName_322_;
v___y_313_ = v___y_318_;
v___y_314_ = v_ref_320_;
v___y_315_ = v_suppressElabErrors_321_;
v___y_316_ = v___x_333_;
goto v___jp_307_;
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_msgData_209_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_338_, lean_object* v_msgData_339_, lean_object* v_severity_340_, lean_object* v_isSilent_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v_severity_boxed_347_; uint8_t v_isSilent_boxed_348_; lean_object* v_res_349_; 
v_severity_boxed_347_ = lean_unbox(v_severity_340_);
v_isSilent_boxed_348_ = lean_unbox(v_isSilent_341_);
v_res_349_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_338_, v_msgData_339_, v_severity_boxed_347_, v_isSilent_boxed_348_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v_ref_338_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(lean_object* v_msgData_350_, uint8_t v_severity_351_, uint8_t v_isSilent_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_ref_362_; lean_object* v___x_363_; 
v_ref_362_ = lean_ctor_get(v___y_359_, 2);
v___x_363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_362_, v_msgData_350_, v_severity_351_, v_isSilent_352_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1___boxed(lean_object* v_msgData_364_, lean_object* v_severity_365_, lean_object* v_isSilent_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v_severity_boxed_376_; uint8_t v_isSilent_boxed_377_; lean_object* v_res_378_; 
v_severity_boxed_376_ = lean_unbox(v_severity_365_);
v_isSilent_boxed_377_ = lean_unbox(v_isSilent_366_);
v_res_378_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v_msgData_364_, v_severity_boxed_376_, v_isSilent_boxed_377_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1));
v___x_383_ = l_Lean_MessageData_ofFormat(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(32u);
v___x_385_ = lean_mk_empty_array_with_capacity(v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7));
v___x_393_ = l_Lean_MessageData_ofFormat(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_397_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_398_ = lean_unsigned_to_nat(39u);
v___x_399_ = lean_unsigned_to_nat(52u);
v___x_400_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_401_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_402_ = l_mkPanicMessageWithDecl(v___x_401_, v___x_400_, v___x_399_, v___x_398_, v___x_397_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_404_ = lean_unsigned_to_nat(37u);
v___x_405_ = lean_unsigned_to_nat(44u);
v___x_406_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10));
v___x_407_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_408_ = l_mkPanicMessageWithDecl(v___x_407_, v___x_406_, v___x_405_, v___x_404_, v___x_403_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___x_413_, uint8_t v___x_414_, lean_object* v___x_415_, lean_object* v_val_416_, lean_object* v_x_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_428_ = 2;
v___x_429_ = 0;
v___x_430_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_427_, v___x_428_, v___x_429_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_tacSnap_x3f_431_; 
lean_dec_ref_known(v___x_430_, 1);
v_tacSnap_x3f_431_ = lean_ctor_get(v___y_420_, 6);
if (lean_obj_tag(v_tacSnap_x3f_431_) == 1)
{
lean_object* v_val_432_; lean_object* v___x_433_; 
v_val_432_ = lean_ctor_get(v_tacSnap_x3f_431_, 0);
v___x_433_ = l_Lean_Core_getMessageLog___redArg(v___y_425_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v_new_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint64_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_toCold_457_; lean_object* v_cancelTk_x3f_458_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_434_);
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_439_ = ((size_t)5ULL);
lean_inc_n(v___x_409_, 2);
v___x_440_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_437_);
lean_ctor_set(v___x_440_, 2, v___x_409_);
lean_ctor_set(v___x_440_, 3, v___x_409_);
lean_ctor_set_usize(v___x_440_, 4, v___x_439_);
v_new_441_ = lean_ctor_get(v_val_432_, 1);
v___x_442_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4));
v___x_443_ = l_Lean_Name_mkStr5(v___x_410_, v___x_411_, v___x_412_, v___x_413_, v___x_442_);
v___x_444_ = l_Lean_Name_toString(v___x_443_, v___x_414_);
v___x_445_ = lean_box(0);
v___x_446_ = 0ULL;
v___x_447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_447_, 0, v___x_440_);
lean_ctor_set_uint64(v___x_447_, sizeof(void*)*1, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_435_);
lean_ctor_set(v___x_448_, 2, v___x_445_);
lean_ctor_set(v___x_448_, 3, v___x_447_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*4, v___x_429_);
v___x_449_ = lean_box(0);
v___x_450_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_415_);
v___x_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_451_, 0, v___x_448_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_445_);
lean_ctor_set(v___x_451_, 3, v___x_450_);
v___x_452_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_mk_empty_array_with_capacity(v___x_409_);
lean_dec(v___x_409_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_io_promise_resolve(v___x_455_, v_new_441_);
v_toCold_457_ = lean_ctor_get(v___y_424_, 0);
v_cancelTk_x3f_458_ = lean_ctor_get(v_toCold_457_, 10);
if (lean_obj_tag(v_cancelTk_x3f_458_) == 1)
{
lean_object* v_ref_459_; lean_object* v_val_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_ref_459_ = lean_ctor_get(v___y_424_, 2);
v_val_460_ = lean_ctor_get(v_cancelTk_x3f_458_, 0);
v___x_461_ = lean_box(0);
v___x_462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_460_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_495_; 
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v___x_462_, 0);
lean_dec(v_unused_496_);
v___x_464_ = v___x_462_;
v_isShared_465_ = v_isSharedCheck_495_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_462_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_495_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_467_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref_known(v___x_467_, 1);
lean_del_object(v___x_464_);
v___x_468_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_469_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_468_, v___x_428_, v___x_429_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_479_; 
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v___x_469_, 0);
lean_dec(v_unused_480_);
v___x_471_ = v___x_469_;
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
else
{
lean_dec(v___x_469_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_io_promise_resolve(v___x_461_, v_val_416_);
v___x_474_ = l_IO_CancelToken_isSet(v_val_460_);
if (v___x_474_ == 0)
{
lean_object* v___x_476_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_461_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_461_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_478_; 
lean_del_object(v___x_471_);
v___x_478_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_478_;
}
}
}
else
{
return v___x_469_;
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_494_; 
v_a_481_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_494_ == 0)
{
v___x_483_ = v___x_467_;
v_isShared_484_ = v_isSharedCheck_494_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_467_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_494_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_io_error_to_string(v_a_481_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 3);
lean_ctor_set(v___x_464_, 0, v___x_485_);
v___x_487_ = v___x_464_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_493_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = l_Lean_MessageData_ofFormat(v___x_487_);
lean_inc(v_ref_459_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_ref_459_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_489_);
v___x_491_ = v___x_483_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
else
{
return v___x_462_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12);
v___x_498_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_497_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v___x_498_;
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec(v___x_409_);
v_a_499_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_433_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_433_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec(v___x_409_);
v___x_507_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13);
v___x_508_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_507_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v___x_508_;
}
}
else
{
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec(v___x_409_);
return v___x_430_;
}
}
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
uint8_t v___x_14687__boxed_527_; lean_object* v_res_528_; 
v___x_14687__boxed_527_ = lean_unbox(v___x_514_);
v_res_528_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(v___x_509_, v___x_510_, v___x_511_, v___x_512_, v___x_513_, v___x_14687__boxed_527_, v___x_515_, v_val_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(lean_object* v_x_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
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
lean_object* v___x_568_; lean_object* v___x_8806__overap_569_; lean_object* v___x_570_; 
lean_dec(v___x_553_);
v___x_568_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_8806__overap_569_ = lean_dbg_trace(v___x_568_, v___f_551_);
lean_inc(v_a_538_);
lean_inc_ref(v_a_537_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
v___x_570_ = lean_apply_9(v___x_8806__overap_569_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, lean_box(0));
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(v_x_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(lean_object* v_val_584_, lean_object* v_inst_585_, lean_object* v_a_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_584_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(lean_object* v_val_597_, lean_object* v_inst_598_, lean_object* v_a_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(v_val_597_, v_inst_598_, v_a_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v_val_597_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(lean_object* v_ref_610_, lean_object* v_msgData_611_, uint8_t v_severity_612_, uint8_t v_isSilent_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_610_, v_msgData_611_, v_severity_612_, v_isSilent_613_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(lean_object* v_ref_624_, lean_object* v_msgData_625_, lean_object* v_severity_626_, lean_object* v_isSilent_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
uint8_t v_severity_boxed_637_; uint8_t v_isSilent_boxed_638_; lean_object* v_res_639_; 
v_severity_boxed_637_ = lean_unbox(v_severity_626_);
v_isSilent_boxed_638_ = lean_unbox(v_isSilent_627_);
v_res_639_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(v_ref_624_, v_msgData_625_, v_severity_boxed_637_, v_isSilent_boxed_638_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v_ref_624_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_box(0);
v___x_642_ = lean_st_mk_ref(v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2____boxed(lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk(){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_fst_651_; lean_object* v_snd_652_; 
v___x_647_ = l_IO_CancelToken_new();
v___x_648_ = l_Lean_Server_Test_Cancel_unblockedCancelTkRef;
v___x_649_ = lean_st_ref_take(v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_654_; 
lean_inc_ref(v___x_647_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_647_);
v_fst_651_ = v___x_647_;
v_snd_652_ = v___x_654_;
goto v___jp_650_;
}
else
{
lean_object* v_val_655_; 
lean_dec_ref(v___x_647_);
v_val_655_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_655_);
v_fst_651_ = v_val_655_;
v_snd_652_ = v___x_649_;
goto v___jp_650_;
}
v___jp_650_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_st_ref_put(v___x_648_, v_snd_652_);
return v_fst_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk___boxed(lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg(){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_box(0);
v___x_676_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
v___x_677_ = l_IO_CancelToken_isSet(v___x_676_);
lean_dec_ref(v___x_676_);
if (v___x_677_ == 0)
{
uint32_t v___x_678_; lean_object* v___x_679_; 
v___x_678_ = 30;
v___x_679_ = l_IO_sleep(v___x_678_);
goto _start;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_675_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v_res_683_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_687_ = lean_unsigned_to_nat(37u);
v___x_688_ = lean_unsigned_to_nat(89u);
v___x_689_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_690_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_691_ = l_mkPanicMessageWithDecl(v___x_690_, v___x_689_, v___x_688_, v___x_687_, v___x_686_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v___x_696_, uint8_t v___x_697_, lean_object* v___x_698_, lean_object* v_val_699_, lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; uint8_t v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; 
v___x_710_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_711_ = 2;
v___x_712_ = 0;
v___x_713_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_710_, v___x_711_, v___x_712_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_783_; 
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_784_);
v___x_715_ = v___x_713_;
v_isShared_716_ = v_isSharedCheck_783_;
goto v_resetjp_714_;
}
else
{
lean_dec(v___x_713_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_783_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_tacSnap_x3f_717_; 
v_tacSnap_x3f_717_ = lean_ctor_get(v___y_703_, 6);
if (lean_obj_tag(v_tacSnap_x3f_717_) == 1)
{
lean_object* v_val_718_; lean_object* v___x_719_; 
v_val_718_ = lean_ctor_get(v_tacSnap_x3f_717_, 0);
v___x_719_ = l_Lean_Core_getMessageLog___redArg(v___y_708_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; size_t v___x_725_; lean_object* v___x_726_; lean_object* v_new_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint64_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_720_);
v___x_722_ = lean_unsigned_to_nat(32u);
v___x_723_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
v___x_725_ = ((size_t)5ULL);
lean_inc_n(v___x_692_, 2);
v___x_726_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_723_);
lean_ctor_set(v___x_726_, 2, v___x_692_);
lean_ctor_set(v___x_726_, 3, v___x_692_);
lean_ctor_set_usize(v___x_726_, 4, v___x_725_);
v_new_727_ = lean_ctor_get(v_val_718_, 1);
v___x_728_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0));
v___x_729_ = l_Lean_Name_mkStr5(v___x_693_, v___x_694_, v___x_695_, v___x_696_, v___x_728_);
v___x_730_ = l_Lean_Name_toString(v___x_729_, v___x_697_);
v___x_731_ = lean_box(0);
v___x_732_ = 0ULL;
v___x_733_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_733_, 0, v___x_726_);
lean_ctor_set_uint64(v___x_733_, sizeof(void*)*1, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_734_, 0, v___x_730_);
lean_ctor_set(v___x_734_, 1, v___x_721_);
lean_ctor_set(v___x_734_, 2, v___x_731_);
lean_ctor_set(v___x_734_, 3, v___x_733_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*4, v___x_712_);
v___x_735_ = lean_box(0);
v___x_736_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_698_);
v___x_737_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_737_, 0, v___x_734_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_731_);
lean_ctor_set(v___x_737_, 3, v___x_736_);
v___x_738_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_692_);
lean_dec(v___x_692_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_io_promise_resolve(v___x_741_, v_new_727_);
v___x_743_ = lean_box(0);
v___x_744_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_771_; 
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_772_);
v___x_746_ = v___x_744_;
v_isShared_747_ = v_isSharedCheck_771_;
goto v_resetjp_745_;
}
else
{
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_771_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
uint8_t v___x_748_; 
v___x_748_ = l_IO_CancelToken_isSet(v_val_699_);
if (v___x_748_ == 0)
{
lean_object* v___x_750_; 
lean_del_object(v___x_715_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_743_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_743_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v_ref_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_del_object(v___x_746_);
v_ref_752_ = lean_ctor_get(v___y_707_, 2);
v___x_753_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_754_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref_known(v___x_754_, 1);
lean_del_object(v___x_715_);
v___x_755_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_756_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_755_, v___x_711_, v___x_712_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_756_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_770_; 
v_a_757_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_770_ == 0)
{
v___x_759_ = v___x_754_;
v_isShared_760_ = v_isSharedCheck_770_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_770_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_io_error_to_string(v_a_757_);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 3);
lean_ctor_set(v___x_715_, 0, v___x_761_);
v___x_763_ = v___x_715_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_769_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_764_ = l_Lean_MessageData_ofFormat(v___x_763_);
lean_inc(v_ref_752_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_ref_752_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_765_);
v___x_767_ = v___x_759_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_715_);
return v___x_744_;
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_715_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec(v___x_692_);
v_a_773_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_719_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_719_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_del_object(v___x_715_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec(v___x_692_);
v___x_781_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2);
v___x_782_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_781_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_782_;
}
}
}
else
{
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec(v___x_692_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_785_ = _args[0];
lean_object* v___x_786_ = _args[1];
lean_object* v___x_787_ = _args[2];
lean_object* v___x_788_ = _args[3];
lean_object* v___x_789_ = _args[4];
lean_object* v___x_790_ = _args[5];
lean_object* v___x_791_ = _args[6];
lean_object* v_val_792_ = _args[7];
lean_object* v_x_793_ = _args[8];
lean_object* v___y_794_ = _args[9];
lean_object* v___y_795_ = _args[10];
lean_object* v___y_796_ = _args[11];
lean_object* v___y_797_ = _args[12];
lean_object* v___y_798_ = _args[13];
lean_object* v___y_799_ = _args[14];
lean_object* v___y_800_ = _args[15];
lean_object* v___y_801_ = _args[16];
lean_object* v___y_802_ = _args[17];
_start:
{
uint8_t v___x_6308__boxed_803_; lean_object* v_res_804_; 
v___x_6308__boxed_803_ = lean_unbox(v___x_790_);
v_res_804_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(v___x_785_, v___x_786_, v___x_787_, v___x_788_, v___x_789_, v___x_6308__boxed_803_, v___x_791_, v_val_792_, v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_val_792_);
return v_res_804_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_805_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_806_ = lean_unsigned_to_nat(39u);
v___x_807_ = lean_unsigned_to_nat(84u);
v___x_808_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1));
v___x_809_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_810_ = l_mkPanicMessageWithDecl(v___x_809_, v___x_808_, v___x_807_, v___x_806_, v___x_805_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(lean_object* v_x_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_821_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_822_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_823_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_824_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_825_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1));
v___x_826_ = l_Lean_Syntax_isOfKind(v_x_811_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_827_;
}
else
{
lean_object* v_toCold_828_; lean_object* v_cancelTk_x3f_829_; 
v_toCold_828_ = lean_ctor_get(v_a_818_, 0);
v_cancelTk_x3f_829_ = lean_ctor_get(v_toCold_828_, 10);
if (lean_obj_tag(v_cancelTk_x3f_829_) == 1)
{
lean_object* v_val_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_5777__overap_836_; lean_object* v___x_837_; 
v_val_830_ = lean_ctor_get(v_cancelTk_x3f_829_, 0);
v___x_831_ = l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_box(v___x_826_);
lean_inc(v_val_830_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed), 18, 8);
lean_closure_set(v___f_834_, 0, v___x_832_);
lean_closure_set(v___f_834_, 1, v___x_821_);
lean_closure_set(v___f_834_, 2, v___x_822_);
lean_closure_set(v___f_834_, 3, v___x_823_);
lean_closure_set(v___f_834_, 4, v___x_824_);
lean_closure_set(v___f_834_, 5, v___x_833_);
lean_closure_set(v___f_834_, 6, v___x_831_);
lean_closure_set(v___f_834_, 7, v_val_830_);
v___x_835_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_5777__overap_836_ = lean_dbg_trace(v___x_835_, v___f_834_);
lean_inc(v_a_819_);
lean_inc_ref(v_a_818_);
lean_inc(v_a_817_);
lean_inc_ref(v_a_816_);
lean_inc(v_a_815_);
lean_inc_ref(v_a_814_);
lean_inc(v_a_813_);
lean_inc_ref(v_a_812_);
v___x_837_ = lean_apply_9(v___x_5777__overap_836_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, lean_box(0));
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0);
v___x_839_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_838_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(v_x_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(lean_object* v_inst_851_, lean_object* v_a_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(lean_object* v_inst_863_, lean_object* v_a_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(v_inst_863_, v_a_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_874_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(lean_object* v_msg_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_4703__overap_901_; lean_object* v___x_902_; 
v___x_900_ = lean_obj_once(&l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0, &l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0);
v___x_4703__overap_901_ = lean_panic_fn_borrowed(v___x_900_, v_msg_892_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
v___x_902_ = lean_apply_7(v___x_4703__overap_901_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, lean_box(0));
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___boxed(lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(lean_object* v_ref_912_, lean_object* v_msgData_913_, uint8_t v_severity_914_, uint8_t v_isSilent_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___y_922_; lean_object* v___y_923_; uint8_t v___y_924_; lean_object* v___y_925_; uint8_t v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v_currNamespace_929_; lean_object* v_openDecls_930_; lean_object* v___y_931_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; uint8_t v___y_961_; uint8_t v___y_962_; uint8_t v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; uint8_t v___y_988_; uint8_t v___y_989_; uint8_t v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; uint8_t v___y_1003_; lean_object* v___y_1004_; uint8_t v___y_1005_; uint8_t v___x_1010_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; uint8_t v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1020_; uint8_t v___y_1022_; uint8_t v___x_1040_; 
v___x_1010_ = 2;
v___x_1040_ = l_Lean_instBEqMessageSeverity_beq(v_severity_914_, v___x_1010_);
if (v___x_1040_ == 0)
{
v___y_1022_ = v___x_1040_;
goto v___jp_1021_;
}
else
{
uint8_t v___x_1041_; 
lean_inc_ref(v_msgData_913_);
v___x_1041_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_913_);
v___y_1022_ = v___x_1041_;
goto v___jp_1021_;
}
v___jp_921_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_env_936_; lean_object* v_nextMacroScope_937_; lean_object* v_ngen_938_; lean_object* v_auxDeclNGen_939_; lean_object* v_traceState_940_; lean_object* v_cache_941_; lean_object* v_messages_942_; lean_object* v_infoState_943_; lean_object* v_snapshotTasks_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_955_; 
lean_inc(v_openDecls_930_);
lean_inc(v_currNamespace_929_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_currNamespace_929_);
lean_ctor_set(v___x_932_, 1, v_openDecls_930_);
v___x_933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___y_928_);
lean_inc_ref(v___y_925_);
lean_inc_ref(v___y_923_);
v___x_934_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_934_, 0, v___y_923_);
lean_ctor_set(v___x_934_, 1, v___y_922_);
lean_ctor_set(v___x_934_, 2, v___y_927_);
lean_ctor_set(v___x_934_, 3, v___y_925_);
lean_ctor_set(v___x_934_, 4, v___x_933_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*5, v___y_926_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*5 + 1, v___y_924_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*5 + 2, v_isSilent_915_);
v___x_935_ = lean_st_ref_take(v___y_931_);
v_env_936_ = lean_ctor_get(v___x_935_, 0);
v_nextMacroScope_937_ = lean_ctor_get(v___x_935_, 1);
v_ngen_938_ = lean_ctor_get(v___x_935_, 2);
v_auxDeclNGen_939_ = lean_ctor_get(v___x_935_, 3);
v_traceState_940_ = lean_ctor_get(v___x_935_, 4);
v_cache_941_ = lean_ctor_get(v___x_935_, 5);
v_messages_942_ = lean_ctor_get(v___x_935_, 6);
v_infoState_943_ = lean_ctor_get(v___x_935_, 7);
v_snapshotTasks_944_ = lean_ctor_get(v___x_935_, 8);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_955_ == 0)
{
v___x_946_ = v___x_935_;
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snapshotTasks_944_);
lean_inc(v_infoState_943_);
lean_inc(v_messages_942_);
lean_inc(v_cache_941_);
lean_inc(v_traceState_940_);
lean_inc(v_auxDeclNGen_939_);
lean_inc(v_ngen_938_);
lean_inc(v_nextMacroScope_937_);
lean_inc(v_env_936_);
lean_dec(v___x_935_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = lean_box(0);
v___x_949_ = l_Lean_MessageLog_add(v___x_934_, v_messages_942_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 6, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_env_936_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_nextMacroScope_937_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_ngen_938_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_auxDeclNGen_939_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_traceState_940_);
lean_ctor_set(v_reuseFailAlloc_954_, 5, v_cache_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 6, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_954_, 7, v_infoState_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 8, v_snapshotTasks_944_);
v___x_951_ = v_reuseFailAlloc_954_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_st_ref_put(v___y_931_, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_948_);
return v___x_953_;
}
}
}
v___jp_956_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_982_; 
v___x_967_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_913_);
v___x_968_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_967_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_982_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_inc_ref_n(v___y_964_, 2);
v___x_973_ = l_Lean_FileMap_toPosition(v___y_964_, v___y_965_);
lean_dec(v___y_965_);
v___x_974_ = l_Lean_FileMap_toPosition(v___y_964_, v___y_966_);
lean_dec(v___y_966_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_962_ == 0)
{
lean_del_object(v___x_971_);
lean_dec_ref(v___y_957_);
v___y_922_ = v___x_973_;
v___y_923_ = v___y_960_;
v___y_924_ = v___y_961_;
v___y_925_ = v___x_976_;
v___y_926_ = v___y_963_;
v___y_927_ = v___x_975_;
v___y_928_ = v_a_969_;
v_currNamespace_929_ = v___y_958_;
v_openDecls_930_ = v___y_959_;
v___y_931_ = v___y_919_;
goto v___jp_921_;
}
else
{
uint8_t v___x_977_; 
lean_inc(v_a_969_);
v___x_977_ = l_Lean_MessageData_hasTag(v___y_957_, v_a_969_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_980_; 
lean_dec_ref_known(v___x_975_, 1);
lean_dec_ref(v___x_973_);
lean_dec(v_a_969_);
v___x_978_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_978_);
v___x_980_ = v___x_971_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_del_object(v___x_971_);
v___y_922_ = v___x_973_;
v___y_923_ = v___y_960_;
v___y_924_ = v___y_961_;
v___y_925_ = v___x_976_;
v___y_926_ = v___y_963_;
v___y_927_ = v___x_975_;
v___y_928_ = v_a_969_;
v_currNamespace_929_ = v___y_958_;
v_openDecls_930_ = v___y_959_;
v___y_931_ = v___y_919_;
goto v___jp_921_;
}
}
}
}
v___jp_983_:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Syntax_getTailPos_x3f(v___y_992_, v___y_990_);
lean_dec(v___y_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_inc(v___y_993_);
v___y_957_ = v___y_984_;
v___y_958_ = v___y_985_;
v___y_959_ = v___y_986_;
v___y_960_ = v___y_987_;
v___y_961_ = v___y_988_;
v___y_962_ = v___y_989_;
v___y_963_ = v___y_990_;
v___y_964_ = v___y_991_;
v___y_965_ = v___y_993_;
v___y_966_ = v___y_993_;
goto v___jp_956_;
}
else
{
lean_object* v_val_995_; 
v_val_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_994_, 1);
v___y_957_ = v___y_984_;
v___y_958_ = v___y_985_;
v___y_959_ = v___y_986_;
v___y_960_ = v___y_987_;
v___y_961_ = v___y_988_;
v___y_962_ = v___y_989_;
v___y_963_ = v___y_990_;
v___y_964_ = v___y_991_;
v___y_965_ = v___y_993_;
v___y_966_ = v_val_995_;
goto v___jp_956_;
}
}
v___jp_996_:
{
lean_object* v_ref_1006_; lean_object* v___x_1007_; 
v_ref_1006_ = l_Lean_replaceRef(v_ref_912_, v___y_1000_);
v___x_1007_ = l_Lean_Syntax_getPos_x3f(v_ref_1006_, v___y_1003_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_unsigned_to_nat(0u);
v___y_984_ = v___y_997_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_999_;
v___y_987_ = v___y_1001_;
v___y_988_ = v___y_1005_;
v___y_989_ = v___y_1002_;
v___y_990_ = v___y_1003_;
v___y_991_ = v___y_1004_;
v___y_992_ = v_ref_1006_;
v___y_993_ = v___x_1008_;
goto v___jp_983_;
}
else
{
lean_object* v_val_1009_; 
v_val_1009_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v___x_1007_, 1);
v___y_984_ = v___y_997_;
v___y_985_ = v___y_998_;
v___y_986_ = v___y_999_;
v___y_987_ = v___y_1001_;
v___y_988_ = v___y_1005_;
v___y_989_ = v___y_1002_;
v___y_990_ = v___y_1003_;
v___y_991_ = v___y_1004_;
v___y_992_ = v_ref_1006_;
v___y_993_ = v_val_1009_;
goto v___jp_983_;
}
}
v___jp_1011_:
{
if (v___y_1020_ == 0)
{
v___y_997_ = v___y_1013_;
v___y_998_ = v___y_1015_;
v___y_999_ = v___y_1016_;
v___y_1000_ = v___y_1017_;
v___y_1001_ = v___y_1012_;
v___y_1002_ = v___y_1018_;
v___y_1003_ = v___y_1019_;
v___y_1004_ = v___y_1014_;
v___y_1005_ = v_severity_914_;
goto v___jp_996_;
}
else
{
v___y_997_ = v___y_1013_;
v___y_998_ = v___y_1015_;
v___y_999_ = v___y_1016_;
v___y_1000_ = v___y_1017_;
v___y_1001_ = v___y_1012_;
v___y_1002_ = v___y_1018_;
v___y_1003_ = v___y_1019_;
v___y_1004_ = v___y_1014_;
v___y_1005_ = v___x_1010_;
goto v___jp_996_;
}
}
v___jp_1021_:
{
if (v___y_1022_ == 0)
{
lean_object* v_toCold_1023_; lean_object* v_ref_1024_; uint8_t v_suppressElabErrors_1025_; lean_object* v_fileName_1026_; lean_object* v_fileMap_1027_; lean_object* v_options_1028_; lean_object* v_currNamespace_1029_; lean_object* v_openDecls_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; 
v_toCold_1023_ = lean_ctor_get(v___y_918_, 0);
v_ref_1024_ = lean_ctor_get(v___y_918_, 2);
v_suppressElabErrors_1025_ = lean_ctor_get_uint8(v___y_918_, sizeof(void*)*3 + 1);
v_fileName_1026_ = lean_ctor_get(v_toCold_1023_, 0);
v_fileMap_1027_ = lean_ctor_get(v_toCold_1023_, 1);
v_options_1028_ = lean_ctor_get(v_toCold_1023_, 2);
v_currNamespace_1029_ = lean_ctor_get(v_toCold_1023_, 4);
v_openDecls_1030_ = lean_ctor_get(v_toCold_1023_, 5);
v___x_1031_ = lean_box(v_suppressElabErrors_1025_);
v___x_1032_ = lean_box(v___y_1022_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1033_, 0, v___x_1031_);
lean_closure_set(v___f_1033_, 1, v___x_1032_);
v___x_1034_ = 1;
v___x_1035_ = l_Lean_instBEqMessageSeverity_beq(v_severity_914_, v___x_1034_);
if (v___x_1035_ == 0)
{
v___y_1012_ = v_fileName_1026_;
v___y_1013_ = v___f_1033_;
v___y_1014_ = v_fileMap_1027_;
v___y_1015_ = v_currNamespace_1029_;
v___y_1016_ = v_openDecls_1030_;
v___y_1017_ = v_ref_1024_;
v___y_1018_ = v_suppressElabErrors_1025_;
v___y_1019_ = v___y_1022_;
v___y_1020_ = v___x_1035_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = l_Lean_warningAsError;
v___x_1037_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_1028_, v___x_1036_);
v___y_1012_ = v_fileName_1026_;
v___y_1013_ = v___f_1033_;
v___y_1014_ = v_fileMap_1027_;
v___y_1015_ = v_currNamespace_1029_;
v___y_1016_ = v_openDecls_1030_;
v___y_1017_ = v_ref_1024_;
v___y_1018_ = v_suppressElabErrors_1025_;
v___y_1019_ = v___y_1022_;
v___y_1020_ = v___x_1037_;
goto v___jp_1011_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref(v_msgData_913_);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(lean_object* v_ref_1042_, lean_object* v_msgData_1043_, lean_object* v_severity_1044_, lean_object* v_isSilent_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_severity_boxed_1051_; uint8_t v_isSilent_boxed_1052_; lean_object* v_res_1053_; 
v_severity_boxed_1051_ = lean_unbox(v_severity_1044_);
v_isSilent_boxed_1052_ = lean_unbox(v_isSilent_1045_);
v_res_1053_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1042_, v_msgData_1043_, v_severity_boxed_1051_, v_isSilent_boxed_1052_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v_ref_1042_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(lean_object* v_msgData_1054_, uint8_t v_severity_1055_, uint8_t v_isSilent_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_ref_1064_; lean_object* v___x_1065_; 
v_ref_1064_ = lean_ctor_get(v___y_1061_, 2);
v___x_1065_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1064_, v_msgData_1054_, v_severity_1055_, v_isSilent_1056_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(lean_object* v_msgData_1066_, lean_object* v_severity_1067_, lean_object* v_isSilent_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v_severity_boxed_1076_; uint8_t v_isSilent_boxed_1077_; lean_object* v_res_1078_; 
v_severity_boxed_1076_ = lean_unbox(v_severity_1067_);
v_isSilent_boxed_1077_ = lean_unbox(v_isSilent_1068_);
v_res_1078_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v_msgData_1066_, v_severity_boxed_1076_, v_isSilent_boxed_1077_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg(){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
v___x_1082_ = l_IO_CancelToken_isSet(v___x_1081_);
lean_dec_ref(v___x_1081_);
if (v___x_1082_ == 0)
{
uint32_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = 30;
v___x_1084_ = l_IO_sleep(v___x_1083_);
goto _start;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1080_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v_res_1088_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1090_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_1091_ = lean_unsigned_to_nat(41u);
v___x_1092_ = lean_unsigned_to_nat(113u);
v___x_1093_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0));
v___x_1094_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_1095_ = l_mkPanicMessageWithDecl(v___x_1094_, v___x_1093_, v___x_1092_, v___x_1091_, v___x_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_toCold_1104_; lean_object* v_cancelTk_x3f_1105_; 
v_toCold_1104_ = lean_ctor_get(v___y_1101_, 0);
v_cancelTk_x3f_1105_ = lean_ctor_get(v_toCold_1104_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1105_) == 1)
{
lean_object* v_ref_1106_; lean_object* v_val_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_ref_1106_ = lean_ctor_get(v___y_1101_, 2);
v_val_1107_ = lean_ctor_get(v_cancelTk_x3f_1105_, 0);
v___x_1108_ = lean_box(0);
v___x_1109_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1135_; 
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1109_, 0);
lean_dec(v_unused_1136_);
v___x_1111_ = v___x_1109_;
v_isShared_1112_ = v_isSharedCheck_1135_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v___x_1109_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1135_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_IO_CancelToken_isSet(v_val_1107_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1115_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1108_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1108_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_del_object(v___x_1111_);
v___x_1117_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_1118_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; uint8_t v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref_known(v___x_1118_, 1);
v___x_1119_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_1120_ = 2;
v___x_1121_ = 0;
v___x_1122_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1119_, v___x_1120_, v___x_1121_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1134_; 
v_a_1123_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1125_ = v___x_1118_;
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1118_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1127_ = lean_io_error_to_string(v_a_1123_);
v___x_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_ofFormat(v___x_1128_);
lean_inc(v_ref_1106_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_ref_1106_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1130_);
v___x_1132_ = v___x_1125_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
else
{
return v___x_1109_;
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1);
v___x_1138_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1137_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed(lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(v_x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1147_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(lean_object* v_x_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1));
v___x_1169_ = l_Lean_Syntax_isOfKind(v_x_1158_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1170_;
}
else
{
lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1171_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0));
v___x_1172_ = l_IO_CancelToken_new();
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2));
v___x_1175_ = l_Lean_Name_toString(v___x_1174_, v___x_1169_);
lean_inc_ref(v___x_1173_);
v___x_1176_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1171_, v___x_1173_, v___x_1175_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_apply_1(v_a_1177_, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_io_as_task(v___x_1179_, v___x_1180_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v___x_1173_);
lean_ctor_set(v___x_1184_, 3, v___x_1181_);
v___x_1185_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1184_, v_a_1166_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref_known(v___x_1185_, 1);
v___x_1186_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1187_ = 2;
v___x_1188_ = 0;
v___x_1189_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1186_, v___x_1187_, v___x_1188_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
return v___x_1189_;
}
else
{
return v___x_1185_;
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref_known(v___x_1173_, 1);
v_a_1190_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1176_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1176_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___boxed(lean_object* v_x_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(v_x_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(lean_object* v_inst_1209_, lean_object* v_a_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(lean_object* v_inst_1219_, lean_object* v_a_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(v_inst_1219_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(lean_object* v_ref_1229_, lean_object* v_msgData_1230_, uint8_t v_severity_1231_, uint8_t v_isSilent_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_1229_, v_msgData_1230_, v_severity_1231_, v_isSilent_1232_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1240_;
}
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed(lean_object* v_x_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(v_x_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(lean_object* v_x_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1));
v___x_1308_ = l_Lean_Syntax_isOfKind(v_x_1297_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1309_;
}
else
{
lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___x_103__overap_1312_; lean_object* v___x_1313_; 
v___f_1310_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0));
v___x_1311_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1));
v___x_103__overap_1312_ = lean_dbg_trace(v___x_1311_, v___f_1310_);
lean_inc(v_a_1305_);
lean_inc_ref(v_a_1304_);
lean_inc(v_a_1303_);
lean_inc_ref(v_a_1302_);
lean_inc(v_a_1301_);
lean_inc_ref(v_a_1300_);
lean_inc(v_a_1299_);
lean_inc_ref(v_a_1298_);
v___x_1313_ = lean_apply_9(v___x_103__overap_1312_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, lean_box(0));
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___boxed(lean_object* v_x_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(v_x_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(lean_object* v_x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_1352_ = 2;
v___x_1353_ = 0;
v___x_1354_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_1351_, v___x_1352_, v___x_1353_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed(lean_object* v_x_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(v_x_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(lean_object* v_val_1366_){
_start:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = l_IO_CancelToken_isSet(v_val_1366_);
if (v___x_1369_ == 0)
{
uint32_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = 30;
v___x_1371_ = l_IO_sleep(v___x_1370_);
goto _start;
}
else
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1368_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(lean_object* v_val_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1374_);
lean_dec_ref(v_val_1374_);
return v_res_1376_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1378_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_1379_ = lean_unsigned_to_nat(41u);
v___x_1380_ = lean_unsigned_to_nat(147u);
v___x_1381_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0));
v___x_1382_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_1383_ = l_mkPanicMessageWithDecl(v___x_1382_, v___x_1381_, v___x_1380_, v___x_1379_, v___x_1378_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(lean_object* v_val_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_toCold_1393_; lean_object* v_cancelTk_x3f_1394_; 
v_toCold_1393_ = lean_ctor_get(v___y_1390_, 0);
v_cancelTk_x3f_1394_ = lean_ctor_get(v_toCold_1393_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1394_) == 1)
{
lean_object* v_ref_1395_; lean_object* v_val_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_ref_1395_ = lean_ctor_get(v___y_1390_, 2);
v_val_1396_ = lean_ctor_get(v_cancelTk_x3f_1394_, 0);
v___x_1397_ = lean_box(0);
v___x_1398_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1396_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1433_; 
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1434_);
v___x_1400_ = v___x_1398_;
v_isShared_1401_ = v_isSharedCheck_1433_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v___x_1398_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1433_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_1403_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1402_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1404_; uint8_t v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref_known(v___x_1403_, 1);
lean_del_object(v___x_1400_);
v___x_1404_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_1405_ = 2;
v___x_1406_ = 0;
v___x_1407_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1404_, v___x_1405_, v___x_1406_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1417_; 
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v___x_1407_, 0);
lean_dec(v_unused_1418_);
v___x_1409_ = v___x_1407_;
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v___x_1407_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_io_promise_resolve(v___x_1397_, v_val_1384_);
v___x_1412_ = l_IO_CancelToken_isSet(v_val_1396_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1414_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1397_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1397_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
lean_object* v___x_1416_; 
lean_del_object(v___x_1409_);
v___x_1416_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1416_;
}
}
}
else
{
return v___x_1407_;
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1432_; 
v_a_1419_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1421_ = v___x_1403_;
v_isShared_1422_ = v_isSharedCheck_1432_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1403_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1432_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_io_error_to_string(v_a_1419_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 3);
lean_ctor_set(v___x_1400_, 0, v___x_1423_);
v___x_1425_ = v___x_1400_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1426_ = l_Lean_MessageData_ofFormat(v___x_1425_);
lean_inc(v_ref_1395_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_ref_1395_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1427_);
v___x_1429_ = v___x_1421_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
}
else
{
return v___x_1398_;
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1);
v___x_1436_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_1435_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(v_val_1437_, v_x_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_val_1437_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(lean_object* v_x_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1));
v___x_1466_ = l_Lean_Syntax_isOfKind(v_x_1455_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1467_;
}
else
{
lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___y_1474_; 
v___f_1468_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
v___x_1469_ = lean_io_promise_new();
lean_inc(v___x_1469_);
v___f_1470_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed), 9, 1);
lean_closure_set(v___f_1470_, 0, v___x_1469_);
v___x_1471_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1472_ = lean_st_ref_take(v___x_1471_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = l_IO_Promise_result_x21___redArg(v___x_1469_);
lean_dec(v___x_1469_);
v___y_1474_ = v___x_1512_;
goto v___jp_1473_;
}
else
{
lean_object* v_val_1513_; 
lean_dec(v___x_1469_);
v_val_1513_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1513_);
v___y_1474_ = v_val_1513_;
goto v___jp_1473_;
}
v___jp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1474_);
v___x_1476_ = lean_st_ref_put(v___x_1471_, v___x_1475_);
if (lean_obj_tag(v___x_1472_) == 1)
{
lean_object* v_val_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v___f_1470_);
v_val_1477_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1479_ = v___x_1472_;
v_isShared_1480_ = v_isSharedCheck_1486_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_val_1477_);
lean_dec(v___x_1472_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1486_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1481_ = lean_io_wait(v_val_1477_);
lean_dec(v___x_1481_);
v___x_1482_ = lean_box(0);
if (v_isShared_1480_ == 0)
{
lean_ctor_set_tag(v___x_1479_, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1482_);
v___x_1484_ = v___x_1479_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v___x_1472_);
v___x_1487_ = l_IO_CancelToken_new();
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2));
v___x_1490_ = l_Lean_Name_toString(v___x_1489_, v___x_1466_);
lean_inc_ref(v___x_1488_);
v___x_1491_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1470_, v___x_1488_, v___x_1490_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_apply_1(v_a_1492_, v___x_1493_);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_io_as_task(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
v___x_1499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
lean_ctor_set(v___x_1499_, 2, v___x_1488_);
lean_ctor_set(v___x_1499_, 3, v___x_1496_);
v___x_1500_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1499_, v_a_1463_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1501_; lean_object* v___x_7024__overap_1502_; lean_object* v___x_1503_; 
lean_dec_ref_known(v___x_1500_, 1);
v___x_1501_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_7024__overap_1502_ = lean_dbg_trace(v___x_1501_, v___f_1468_);
lean_inc(v_a_1463_);
lean_inc_ref(v_a_1462_);
lean_inc(v_a_1461_);
lean_inc_ref(v_a_1460_);
lean_inc(v_a_1459_);
lean_inc_ref(v_a_1458_);
lean_inc(v_a_1457_);
lean_inc_ref(v_a_1456_);
v___x_1503_ = lean_apply_9(v___x_7024__overap_1502_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, lean_box(0));
return v___x_1503_;
}
else
{
return v___x_1500_;
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref_known(v___x_1488_, 1);
v_a_1504_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1491_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1491_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___boxed(lean_object* v_x_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(v_x_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(lean_object* v_val_1525_, lean_object* v_inst_1526_, lean_object* v_a_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1525_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(lean_object* v_val_1536_, lean_object* v_inst_1537_, lean_object* v_a_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(v_val_1536_, v_inst_1537_, v_a_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v_val_1536_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(lean_object* v_val_1563_, lean_object* v_val_1564_, lean_object* v_x_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_1563_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1616_; 
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v___x_1574_, 0);
lean_dec(v_unused_1617_);
v___x_1576_ = v___x_1574_;
v_isShared_1577_ = v_isSharedCheck_1616_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v___x_1574_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1616_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_toCold_1578_; lean_object* v_ref_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_toCold_1578_ = lean_ctor_get(v___y_1570_, 0);
v_ref_1579_ = lean_ctor_get(v___y_1570_, 2);
v___x_1580_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_1581_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; uint8_t v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref_known(v___x_1581_, 1);
lean_del_object(v___x_1576_);
v___x_1582_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_1583_ = 2;
v___x_1584_ = 0;
v___x_1585_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_1582_, v___x_1583_, v___x_1584_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1600_; 
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v___x_1585_, 0);
lean_dec(v_unused_1601_);
v___x_1587_ = v___x_1585_;
v_isShared_1588_ = v_isSharedCheck_1600_;
goto v_resetjp_1586_;
}
else
{
lean_dec(v___x_1585_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1600_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v_cancelTk_x3f_1590_; 
v___x_1589_ = lean_io_promise_resolve(v___x_1573_, v_val_1564_);
v_cancelTk_x3f_1590_ = lean_ctor_get(v_toCold_1578_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1590_) == 1)
{
lean_object* v_val_1591_; uint8_t v___x_1592_; 
v_val_1591_ = lean_ctor_get(v_cancelTk_x3f_1590_, 0);
v___x_1592_ = l_IO_CancelToken_isSet(v_val_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1573_);
v___x_1594_ = v___x_1587_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1573_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
else
{
lean_object* v___x_1596_; 
lean_del_object(v___x_1587_);
v___x_1596_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_1596_;
}
}
else
{
lean_object* v___x_1598_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1573_);
v___x_1598_ = v___x_1587_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1573_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
return v___x_1585_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1615_; 
v_a_1602_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1604_ = v___x_1581_;
v_isShared_1605_ = v_isSharedCheck_1615_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1581_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1615_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_io_error_to_string(v_a_1602_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 3);
lean_ctor_set(v___x_1576_, 0, v___x_1606_);
v___x_1608_ = v___x_1576_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = l_Lean_MessageData_ofFormat(v___x_1608_);
lean_inc(v_ref_1579_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_ref_1579_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1610_);
v___x_1612_ = v___x_1604_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
else
{
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed(lean_object* v_val_1618_, lean_object* v_val_1619_, lean_object* v_x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(v_val_1618_, v_val_1619_, v_x_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v_val_1619_);
lean_dec_ref(v_val_1618_);
return v_res_1628_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1639_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_1640_ = lean_unsigned_to_nat(60u);
v___x_1641_ = lean_unsigned_to_nat(177u);
v___x_1642_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3));
v___x_1643_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_1644_ = l_mkPanicMessageWithDecl(v___x_1643_, v___x_1642_, v___x_1641_, v___x_1640_, v___x_1639_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(lean_object* v_x_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1));
v___x_1656_ = l_Lean_Syntax_isOfKind(v_x_1645_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1657_;
}
else
{
lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___y_1663_; 
v___f_1658_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0));
v___x_1659_ = lean_io_promise_new();
v___x_1660_ = l_Lean_Server_Test_Cancel_onceRef;
v___x_1661_ = lean_st_ref_take(v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = l_IO_Promise_result_x21___redArg(v___x_1659_);
v___y_1663_ = v___x_1705_;
goto v___jp_1662_;
}
else
{
lean_object* v_val_1706_; 
v_val_1706_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1706_);
v___y_1663_ = v_val_1706_;
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1663_);
v___x_1665_ = lean_st_ref_put(v___x_1660_, v___x_1664_);
if (lean_obj_tag(v___x_1661_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v___x_1659_);
v_val_1666_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1668_ = v___x_1661_;
v_isShared_1669_ = v_isSharedCheck_1675_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_val_1666_);
lean_dec(v___x_1661_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1675_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1670_ = lean_io_wait(v_val_1666_);
lean_dec(v___x_1670_);
v___x_1671_ = lean_box(0);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1671_);
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_toCold_1676_; lean_object* v_cancelTk_x3f_1677_; 
lean_dec(v___x_1661_);
v_toCold_1676_ = lean_ctor_get(v_a_1652_, 0);
v_cancelTk_x3f_1677_ = lean_ctor_get(v_toCold_1676_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1677_) == 1)
{
lean_object* v_val_1678_; lean_object* v___f_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_val_1678_ = lean_ctor_get(v_cancelTk_x3f_1677_, 0);
lean_inc(v_val_1678_);
v___f_1679_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed), 10, 2);
lean_closure_set(v___f_1679_, 0, v_val_1678_);
lean_closure_set(v___f_1679_, 1, v___x_1659_);
v___x_1680_ = lean_box(0);
v___x_1681_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1));
v___x_1682_ = l_Lean_Name_toString(v___x_1681_, v___x_1656_);
v___x_1683_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(v___f_1679_, v___x_1680_, v___x_1682_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_apply_1(v_a_1684_, v___x_1685_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = lean_io_as_task(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_1677_);
v___x_1690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1680_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set(v___x_1690_, 2, v_cancelTk_x3f_1677_);
lean_ctor_set(v___x_1690_, 3, v___x_1688_);
v___x_1691_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1690_, v_a_1653_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_6900__overap_1693_; lean_object* v___x_1694_; 
lean_dec_ref_known(v___x_1691_, 1);
v___x_1692_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0));
v___x_6900__overap_1693_ = lean_dbg_trace(v___x_1692_, v___f_1658_);
lean_inc(v_a_1653_);
lean_inc_ref(v_a_1652_);
lean_inc(v_a_1651_);
lean_inc_ref(v_a_1650_);
lean_inc(v_a_1649_);
lean_inc_ref(v_a_1648_);
lean_inc(v_a_1647_);
lean_inc_ref(v_a_1646_);
v___x_1694_ = lean_apply_9(v___x_6900__overap_1693_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, lean_box(0));
return v___x_1694_;
}
else
{
return v___x_1691_;
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1683_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1683_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v___x_1659_);
v___x_1703_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4);
v___x_1704_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_1703_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
return v___x_1704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___boxed(lean_object* v_x_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(v_x_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_st_mk_ref(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg(){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg___boxed(lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(lean_object* v_00_u03b1_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___boxed(lean_object* v_00_u03b1_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(v_00_u03b1_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(lean_object* v_msg_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___f_1771_; lean_object* v___x_3921__overap_1772_; lean_object* v___x_1773_; 
v___f_1771_ = ((lean_object*)(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0));
v___x_3921__overap_1772_ = lean_panic_fn_borrowed(v___f_1771_, v_msg_1767_);
lean_inc(v___y_1769_);
lean_inc_ref(v___y_1768_);
v___x_1773_ = lean_apply_3(v___x_3921__overap_1772_, v___y_1768_, v___y_1769_, lean_box(0));
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___boxed(lean_object* v_msg_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v_msg_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1778_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
lean_ctor_set(v___x_1784_, 2, v___x_1783_);
lean_ctor_set(v___x_1784_, 3, v___x_1783_);
lean_ctor_set(v___x_1784_, 4, v___x_1782_);
lean_ctor_set(v___x_1784_, 5, v___x_1782_);
lean_ctor_set(v___x_1784_, 6, v___x_1782_);
lean_ctor_set(v___x_1784_, 7, v___x_1782_);
lean_ctor_set(v___x_1784_, 8, v___x_1782_);
lean_ctor_set(v___x_1784_, 9, v___x_1782_);
lean_ctor_set(v___x_1784_, 10, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(32u);
v___x_1786_ = lean_mk_empty_array_with_capacity(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4(void){
_start:
{
size_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1788_ = ((size_t)5ULL);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_unsigned_to_nat(32u);
v___x_1791_ = lean_mk_empty_array_with_capacity(v___x_1790_);
v___x_1792_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3);
v___x_1793_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v___x_1791_);
lean_ctor_set(v___x_1793_, 2, v___x_1789_);
lean_ctor_set(v___x_1793_, 3, v___x_1789_);
lean_ctor_set_usize(v___x_1793_, 4, v___x_1788_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_box(1);
v___x_1795_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4);
v___x_1796_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
v___x_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1795_);
lean_ctor_set(v___x_1797_, 2, v___x_1794_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(lean_object* v_msgData_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v_toCold_1803_; lean_object* v_env_1804_; lean_object* v_options_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1802_ = lean_st_ref_get(v___y_1800_);
v_toCold_1803_ = lean_ctor_get(v___y_1799_, 0);
v_env_1804_ = lean_ctor_get(v___x_1802_, 0);
lean_inc_ref(v_env_1804_);
lean_dec(v___x_1802_);
v_options_1805_ = lean_ctor_get(v_toCold_1803_, 2);
v___x_1806_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_1807_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5);
lean_inc_ref(v_options_1805_);
v___x_1808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1808_, 0, v_env_1804_);
lean_ctor_set(v___x_1808_, 1, v___x_1806_);
lean_ctor_set(v___x_1808_, 2, v___x_1807_);
lean_ctor_set(v___x_1808_, 3, v_options_1805_);
v___x_1809_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_msgData_1798_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v_msgData_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(lean_object* v_ref_1816_, lean_object* v_msgData_1817_, uint8_t v_severity_1818_, uint8_t v_isSilent_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; lean_object* v_currNamespace_1831_; lean_object* v_openDecls_1832_; lean_object* v___y_1833_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; uint8_t v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; uint8_t v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; uint8_t v___y_1906_; uint8_t v___y_1907_; uint8_t v___x_1912_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; uint8_t v___y_1922_; uint8_t v___y_1924_; uint8_t v___x_1942_; 
v___x_1912_ = 2;
v___x_1942_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1818_, v___x_1912_);
if (v___x_1942_ == 0)
{
v___y_1924_ = v___x_1942_;
goto v___jp_1923_;
}
else
{
uint8_t v___x_1943_; 
lean_inc_ref(v_msgData_1817_);
v___x_1943_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1817_);
v___y_1924_ = v___x_1943_;
goto v___jp_1923_;
}
v___jp_1823_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_env_1838_; lean_object* v_nextMacroScope_1839_; lean_object* v_ngen_1840_; lean_object* v_auxDeclNGen_1841_; lean_object* v_traceState_1842_; lean_object* v_cache_1843_; lean_object* v_messages_1844_; lean_object* v_infoState_1845_; lean_object* v_snapshotTasks_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1857_; 
lean_inc(v_openDecls_1832_);
lean_inc(v_currNamespace_1831_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_currNamespace_1831_);
lean_ctor_set(v___x_1834_, 1, v_openDecls_1832_);
v___x_1835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___y_1827_);
lean_inc_ref(v___y_1828_);
lean_inc_ref(v___y_1829_);
v___x_1836_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1836_, 0, v___y_1829_);
lean_ctor_set(v___x_1836_, 1, v___y_1826_);
lean_ctor_set(v___x_1836_, 2, v___y_1825_);
lean_ctor_set(v___x_1836_, 3, v___y_1828_);
lean_ctor_set(v___x_1836_, 4, v___x_1835_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*5, v___y_1830_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*5 + 1, v___y_1824_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*5 + 2, v_isSilent_1819_);
v___x_1837_ = lean_st_ref_take(v___y_1833_);
v_env_1838_ = lean_ctor_get(v___x_1837_, 0);
v_nextMacroScope_1839_ = lean_ctor_get(v___x_1837_, 1);
v_ngen_1840_ = lean_ctor_get(v___x_1837_, 2);
v_auxDeclNGen_1841_ = lean_ctor_get(v___x_1837_, 3);
v_traceState_1842_ = lean_ctor_get(v___x_1837_, 4);
v_cache_1843_ = lean_ctor_get(v___x_1837_, 5);
v_messages_1844_ = lean_ctor_get(v___x_1837_, 6);
v_infoState_1845_ = lean_ctor_get(v___x_1837_, 7);
v_snapshotTasks_1846_ = lean_ctor_get(v___x_1837_, 8);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1848_ = v___x_1837_;
v_isShared_1849_ = v_isSharedCheck_1857_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_snapshotTasks_1846_);
lean_inc(v_infoState_1845_);
lean_inc(v_messages_1844_);
lean_inc(v_cache_1843_);
lean_inc(v_traceState_1842_);
lean_inc(v_auxDeclNGen_1841_);
lean_inc(v_ngen_1840_);
lean_inc(v_nextMacroScope_1839_);
lean_inc(v_env_1838_);
lean_dec(v___x_1837_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1857_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_MessageLog_add(v___x_1836_, v_messages_1844_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 6, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_env_1838_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_nextMacroScope_1839_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_ngen_1840_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_auxDeclNGen_1841_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_traceState_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_cache_1843_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_infoState_1845_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v_snapshotTasks_1846_);
v___x_1853_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_st_ref_put(v___y_1833_, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1850_);
return v___x_1855_;
}
}
}
v___jp_1858_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1884_; 
v___x_1869_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1817_);
v___x_1870_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v___x_1869_, v___y_1820_, v___y_1821_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1884_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1884_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_inc_ref_n(v___y_1866_, 2);
v___x_1875_ = l_Lean_FileMap_toPosition(v___y_1866_, v___y_1865_);
lean_dec(v___y_1865_);
v___x_1876_ = l_Lean_FileMap_toPosition(v___y_1866_, v___y_1868_);
lean_dec(v___y_1868_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___x_1878_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0));
if (v___y_1863_ == 0)
{
lean_del_object(v___x_1873_);
lean_dec_ref(v___y_1861_);
v___y_1824_ = v___y_1862_;
v___y_1825_ = v___x_1877_;
v___y_1826_ = v___x_1875_;
v___y_1827_ = v_a_1871_;
v___y_1828_ = v___x_1878_;
v___y_1829_ = v___y_1864_;
v___y_1830_ = v___y_1867_;
v_currNamespace_1831_ = v___y_1859_;
v_openDecls_1832_ = v___y_1860_;
v___y_1833_ = v___y_1821_;
goto v___jp_1823_;
}
else
{
uint8_t v___x_1879_; 
lean_inc(v_a_1871_);
v___x_1879_ = l_Lean_MessageData_hasTag(v___y_1861_, v_a_1871_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec_ref_known(v___x_1877_, 1);
lean_dec_ref(v___x_1875_);
lean_dec(v_a_1871_);
v___x_1880_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1880_);
v___x_1882_ = v___x_1873_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
else
{
lean_del_object(v___x_1873_);
v___y_1824_ = v___y_1862_;
v___y_1825_ = v___x_1877_;
v___y_1826_ = v___x_1875_;
v___y_1827_ = v_a_1871_;
v___y_1828_ = v___x_1878_;
v___y_1829_ = v___y_1864_;
v___y_1830_ = v___y_1867_;
v_currNamespace_1831_ = v___y_1859_;
v_openDecls_1832_ = v___y_1860_;
v___y_1833_ = v___y_1821_;
goto v___jp_1823_;
}
}
}
}
v___jp_1885_:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Syntax_getTailPos_x3f(v___y_1889_, v___y_1894_);
lean_dec(v___y_1889_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_inc(v___y_1895_);
v___y_1859_ = v___y_1886_;
v___y_1860_ = v___y_1887_;
v___y_1861_ = v___y_1888_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1893_;
v___y_1865_ = v___y_1895_;
v___y_1866_ = v___y_1892_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v___y_1895_;
goto v___jp_1858_;
}
else
{
lean_object* v_val_1897_; 
v_val_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___y_1859_ = v___y_1886_;
v___y_1860_ = v___y_1887_;
v___y_1861_ = v___y_1888_;
v___y_1862_ = v___y_1890_;
v___y_1863_ = v___y_1891_;
v___y_1864_ = v___y_1893_;
v___y_1865_ = v___y_1895_;
v___y_1866_ = v___y_1892_;
v___y_1867_ = v___y_1894_;
v___y_1868_ = v_val_1897_;
goto v___jp_1858_;
}
}
v___jp_1898_:
{
lean_object* v_ref_1908_; lean_object* v___x_1909_; 
v_ref_1908_ = l_Lean_replaceRef(v_ref_1816_, v___y_1903_);
v___x_1909_ = l_Lean_Syntax_getPos_x3f(v_ref_1908_, v___y_1906_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_unsigned_to_nat(0u);
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1900_;
v___y_1888_ = v___y_1901_;
v___y_1889_ = v_ref_1908_;
v___y_1890_ = v___y_1907_;
v___y_1891_ = v___y_1902_;
v___y_1892_ = v___y_1905_;
v___y_1893_ = v___y_1904_;
v___y_1894_ = v___y_1906_;
v___y_1895_ = v___x_1910_;
goto v___jp_1885_;
}
else
{
lean_object* v_val_1911_; 
v_val_1911_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v___x_1909_, 1);
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1900_;
v___y_1888_ = v___y_1901_;
v___y_1889_ = v_ref_1908_;
v___y_1890_ = v___y_1907_;
v___y_1891_ = v___y_1902_;
v___y_1892_ = v___y_1905_;
v___y_1893_ = v___y_1904_;
v___y_1894_ = v___y_1906_;
v___y_1895_ = v_val_1911_;
goto v___jp_1885_;
}
}
v___jp_1913_:
{
if (v___y_1922_ == 0)
{
v___y_1899_ = v___y_1914_;
v___y_1900_ = v___y_1915_;
v___y_1901_ = v___y_1916_;
v___y_1902_ = v___y_1919_;
v___y_1903_ = v___y_1920_;
v___y_1904_ = v___y_1918_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1921_;
v___y_1907_ = v_severity_1818_;
goto v___jp_1898_;
}
else
{
v___y_1899_ = v___y_1914_;
v___y_1900_ = v___y_1915_;
v___y_1901_ = v___y_1916_;
v___y_1902_ = v___y_1919_;
v___y_1903_ = v___y_1920_;
v___y_1904_ = v___y_1918_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1921_;
v___y_1907_ = v___x_1912_;
goto v___jp_1898_;
}
}
v___jp_1923_:
{
if (v___y_1924_ == 0)
{
lean_object* v_toCold_1925_; lean_object* v_ref_1926_; uint8_t v_suppressElabErrors_1927_; lean_object* v_fileName_1928_; lean_object* v_fileMap_1929_; lean_object* v_options_1930_; lean_object* v_currNamespace_1931_; lean_object* v_openDecls_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; uint8_t v___x_1936_; uint8_t v___x_1937_; 
v_toCold_1925_ = lean_ctor_get(v___y_1820_, 0);
v_ref_1926_ = lean_ctor_get(v___y_1820_, 2);
v_suppressElabErrors_1927_ = lean_ctor_get_uint8(v___y_1820_, sizeof(void*)*3 + 1);
v_fileName_1928_ = lean_ctor_get(v_toCold_1925_, 0);
v_fileMap_1929_ = lean_ctor_get(v_toCold_1925_, 1);
v_options_1930_ = lean_ctor_get(v_toCold_1925_, 2);
v_currNamespace_1931_ = lean_ctor_get(v_toCold_1925_, 4);
v_openDecls_1932_ = lean_ctor_get(v_toCold_1925_, 5);
v___x_1933_ = lean_box(v_suppressElabErrors_1927_);
v___x_1934_ = lean_box(v___y_1924_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1935_, 0, v___x_1933_);
lean_closure_set(v___f_1935_, 1, v___x_1934_);
v___x_1936_ = 1;
v___x_1937_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1818_, v___x_1936_);
if (v___x_1937_ == 0)
{
v___y_1914_ = v_currNamespace_1931_;
v___y_1915_ = v_openDecls_1932_;
v___y_1916_ = v___f_1935_;
v___y_1917_ = v_fileMap_1929_;
v___y_1918_ = v_fileName_1928_;
v___y_1919_ = v_suppressElabErrors_1927_;
v___y_1920_ = v_ref_1926_;
v___y_1921_ = v___y_1924_;
v___y_1922_ = v___x_1937_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = l_Lean_warningAsError;
v___x_1939_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_1930_, v___x_1938_);
v___y_1914_ = v_currNamespace_1931_;
v___y_1915_ = v_openDecls_1932_;
v___y_1916_ = v___f_1935_;
v___y_1917_ = v_fileMap_1929_;
v___y_1918_ = v_fileName_1928_;
v___y_1919_ = v_suppressElabErrors_1927_;
v___y_1920_ = v_ref_1926_;
v___y_1921_ = v___y_1924_;
v___y_1922_ = v___x_1939_;
goto v___jp_1913_;
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v_msgData_1817_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_1944_, lean_object* v_msgData_1945_, lean_object* v_severity_1946_, lean_object* v_isSilent_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v_severity_boxed_1951_; uint8_t v_isSilent_boxed_1952_; lean_object* v_res_1953_; 
v_severity_boxed_1951_ = lean_unbox(v_severity_1946_);
v_isSilent_boxed_1952_ = lean_unbox(v_isSilent_1947_);
v_res_1953_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1944_, v_msgData_1945_, v_severity_boxed_1951_, v_isSilent_boxed_1952_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v_ref_1944_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(lean_object* v_msgData_1954_, uint8_t v_severity_1955_, uint8_t v_isSilent_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_ref_1960_; lean_object* v___x_1961_; 
v_ref_1960_ = lean_ctor_get(v___y_1957_, 2);
v___x_1961_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_1960_, v_msgData_1954_, v_severity_1955_, v_isSilent_1956_, v___y_1957_, v___y_1958_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2___boxed(lean_object* v_msgData_1962_, lean_object* v_severity_1963_, lean_object* v_isSilent_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v_severity_boxed_1968_; uint8_t v_isSilent_boxed_1969_; lean_object* v_res_1970_; 
v_severity_boxed_1968_ = lean_unbox(v_severity_1963_);
v_isSilent_boxed_1969_ = lean_unbox(v_isSilent_1964_);
v_res_1970_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1962_, v_severity_boxed_1968_, v_isSilent_boxed_1969_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(lean_object* v_msgData_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = 0;
v___x_1976_ = 0;
v___x_1977_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_1971_, v___x_1975_, v___x_1976_, v___y_1972_, v___y_1973_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2___boxed(lean_object* v_msgData_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v_msgData_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(lean_object* v_val_1983_){
_start:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = l_IO_CancelToken_isSet(v_val_1983_);
if (v___x_1986_ == 0)
{
uint32_t v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = 30;
v___x_1988_ = l_IO_sleep(v___x_1987_);
goto _start;
}
else
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1985_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(lean_object* v_val_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1991_);
lean_dec_ref(v_val_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(lean_object* v_val_1994_, lean_object* v_val_1995_, lean_object* v_x_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_1994_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2042_);
v___x_2003_ = v___x_2001_;
v_isShared_2004_ = v_isSharedCheck_2041_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_2001_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2041_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_toCold_2005_; lean_object* v_ref_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_toCold_2005_ = lean_ctor_get(v___y_1997_, 0);
v_ref_2006_ = lean_ctor_get(v___y_1997_, 2);
v___x_2007_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5));
v___x_2008_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec_ref_known(v___x_2008_, 1);
lean_del_object(v___x_2003_);
v___x_2009_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8);
v___x_2010_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_2009_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2025_; 
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2010_, 0);
lean_dec(v_unused_2026_);
v___x_2012_ = v___x_2010_;
v_isShared_2013_ = v_isSharedCheck_2025_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v___x_2010_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2025_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v_cancelTk_x3f_2015_; 
v___x_2014_ = lean_io_promise_resolve(v___x_2000_, v_val_1995_);
v_cancelTk_x3f_2015_ = lean_ctor_get(v_toCold_2005_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2015_) == 1)
{
lean_object* v_val_2016_; uint8_t v___x_2017_; 
v_val_2016_ = lean_ctor_get(v_cancelTk_x3f_2015_, 0);
v___x_2017_ = l_IO_CancelToken_isSet(v_val_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2019_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2000_);
v___x_2019_ = v___x_2012_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2000_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v___x_2021_; 
lean_del_object(v___x_2012_);
v___x_2021_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
return v___x_2021_;
}
}
else
{
lean_object* v___x_2023_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2000_);
v___x_2023_ = v___x_2012_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2000_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
return v___x_2010_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2040_; 
v_a_2027_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2029_ = v___x_2008_;
v_isShared_2030_ = v_isSharedCheck_2040_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2008_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2040_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2031_ = lean_io_error_to_string(v_a_2027_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 3);
lean_ctor_set(v___x_2003_, 0, v___x_2031_);
v___x_2033_ = v___x_2003_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2034_ = l_Lean_MessageData_ofFormat(v___x_2033_);
lean_inc(v_ref_2006_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_ref_2006_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2035_);
v___x_2037_ = v___x_2029_;
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
return v___x_2037_;
}
}
}
}
}
}
else
{
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed(lean_object* v_val_2043_, lean_object* v_val_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(v_val_2043_, v_val_2044_, v_x_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v_val_2044_);
lean_dec_ref(v_val_2043_);
return v_res_2049_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2052_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_2053_ = lean_unsigned_to_nat(44u);
v___x_2054_ = lean_unsigned_to_nat(209u);
v___x_2055_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1));
v___x_2056_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_2057_ = l_mkPanicMessageWithDecl(v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_, v___x_2052_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(lean_object* v___x_2058_, lean_object* v___x_2059_, lean_object* v___x_2060_, lean_object* v___x_2061_, uint8_t v___x_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___y_2070_; 
v___x_2066_ = lean_io_promise_new();
v___x_2067_ = l_Lean_Server_Test_Cancel_cmdOnceRef;
v___x_2068_ = lean_st_ref_take(v___x_2067_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = l_IO_Promise_result_x21___redArg(v___x_2066_);
v___y_2070_ = v___x_2112_;
goto v___jp_2069_;
}
else
{
lean_object* v_val_2113_; 
v_val_2113_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2113_);
v___y_2070_ = v_val_2113_;
goto v___jp_2069_;
}
v___jp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___y_2070_);
v___x_2072_ = lean_st_ref_put(v___x_2067_, v___x_2071_);
if (lean_obj_tag(v___x_2068_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v___x_2066_);
lean_dec_ref(v___y_2063_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v___x_2060_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2058_);
v_val_2073_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2075_ = v___x_2068_;
v_isShared_2076_ = v_isSharedCheck_2082_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_val_2073_);
lean_dec(v___x_2068_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2082_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2077_ = lean_io_wait(v_val_2073_);
lean_dec(v___x_2077_);
v___x_2078_ = lean_box(0);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2078_);
v___x_2080_ = v___x_2075_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_object* v_toCold_2083_; lean_object* v_cancelTk_x3f_2084_; 
lean_dec(v___x_2068_);
v_toCold_2083_ = lean_ctor_get(v___y_2063_, 0);
v_cancelTk_x3f_2084_ = lean_ctor_get(v_toCold_2083_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2084_) == 1)
{
lean_object* v_val_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_val_2085_ = lean_ctor_get(v_cancelTk_x3f_2084_, 0);
lean_inc(v_val_2085_);
v___f_2086_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_2086_, 0, v_val_2085_);
lean_closure_set(v___f_2086_, 1, v___x_2066_);
v___x_2087_ = lean_box(0);
v___x_2088_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0));
v___x_2089_ = l_Lean_Name_mkStr5(v___x_2058_, v___x_2059_, v___x_2060_, v___x_2061_, v___x_2088_);
v___x_2090_ = l_Lean_Name_toString(v___x_2089_, v___x_2062_);
v___x_2091_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_2086_, v___x_2087_, v___x_2090_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_apply_1(v_a_2092_, v___x_2093_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_io_as_task(v___x_2094_, v___x_2095_);
v___x_2097_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
lean_inc_ref(v_cancelTk_x3f_2084_);
v___x_2098_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2087_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
lean_ctor_set(v___x_2098_, 2, v_cancelTk_x3f_2084_);
lean_ctor_set(v___x_2098_, 3, v___x_2096_);
v___x_2099_ = l_Lean_Core_logSnapshotTask___redArg(v___x_2098_, v___y_2064_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec_ref_known(v___x_2099_, 1);
v___x_2100_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
v___x_2101_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_2100_, v___y_2063_, v___y_2064_);
lean_dec_ref(v___y_2063_);
return v___x_2101_;
}
else
{
lean_dec_ref(v___y_2063_);
return v___x_2099_;
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v___y_2063_);
v_a_2102_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2091_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2091_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec(v___x_2066_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v___x_2060_);
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2058_);
v___x_2110_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2);
v___x_2111_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v___x_2110_, v___y_2063_, v___y_2064_);
lean_dec_ref(v___y_2063_);
return v___x_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed(lean_object* v___x_2114_, lean_object* v___x_2115_, lean_object* v___x_2116_, lean_object* v___x_2117_, lean_object* v___x_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v___x_7287__boxed_2122_; lean_object* v_res_2123_; 
v___x_7287__boxed_2122_ = lean_unbox(v___x_2118_);
v_res_2123_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(v___x_2114_, v___x_2115_, v___x_2116_, v___x_2117_, v___x_7287__boxed_2122_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(lean_object* v_x_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2128_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0));
v___x_2129_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1));
v___x_2130_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2));
v___x_2131_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3));
v___x_2132_ = ((lean_object*)(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1));
v___x_2133_ = l_Lean_Syntax_isOfKind(v_x_2124_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_box(v___x_2133_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2136_, 0, v___x_2128_);
lean_closure_set(v___f_2136_, 1, v___x_2129_);
lean_closure_set(v___f_2136_, 2, v___x_2130_);
lean_closure_set(v___f_2136_, 3, v___x_2131_);
lean_closure_set(v___f_2136_, 4, v___x_2135_);
v___x_2137_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_2136_, v_a_2125_, v_a_2126_);
return v___x_2137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___boxed(lean_object* v_x_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(v_x_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(lean_object* v_val_2143_, lean_object* v_inst_2144_, lean_object* v_a_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_2143_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(lean_object* v_val_2150_, lean_object* v_inst_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(v_val_2150_, v_inst_2151_, v_a_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_val_2150_);
return v_res_2156_;
}
}
static lean_object* _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_unsigned_to_nat(16u);
v___x_2159_ = lean_mk_array(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_obj_once(&l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_, &l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_, &l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
v___x_2165_ = lean_st_mk_ref(v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2____boxed(lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(lean_object* v_a_2169_, lean_object* v_b_2170_, lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2171_) == 0)
{
lean_dec(v_b_2170_);
lean_dec_ref(v_a_2169_);
return v_x_2171_;
}
else
{
lean_object* v_key_2172_; lean_object* v_value_2173_; lean_object* v_tail_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2186_; 
v_key_2172_ = lean_ctor_get(v_x_2171_, 0);
v_value_2173_ = lean_ctor_get(v_x_2171_, 1);
v_tail_2174_ = lean_ctor_get(v_x_2171_, 2);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_x_2171_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2176_ = v_x_2171_;
v_isShared_2177_ = v_isSharedCheck_2186_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_tail_2174_);
lean_inc(v_value_2173_);
lean_inc(v_key_2172_);
lean_dec(v_x_2171_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2186_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_string_dec_eq(v_key_2172_, v_a_2169_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_2169_, v_b_2170_, v_tail_2174_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 2, v___x_2179_);
v___x_2181_ = v___x_2176_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_key_2172_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_value_2173_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v___x_2184_; 
lean_dec(v_value_2173_);
lean_dec(v_key_2172_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_b_2170_);
lean_ctor_set(v___x_2176_, 0, v_a_2169_);
v___x_2184_ = v___x_2176_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2169_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_b_2170_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_tail_2174_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 0)
{
return v_x_2187_;
}
else
{
lean_object* v_key_2189_; lean_object* v_value_2190_; lean_object* v_tail_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2214_; 
v_key_2189_ = lean_ctor_get(v_x_2188_, 0);
v_value_2190_ = lean_ctor_get(v_x_2188_, 1);
v_tail_2191_ = lean_ctor_get(v_x_2188_, 2);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2188_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2193_ = v_x_2188_;
v_isShared_2194_ = v_isSharedCheck_2214_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_tail_2191_);
lean_inc(v_value_2190_);
lean_inc(v_key_2189_);
lean_dec(v_x_2188_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2214_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; uint64_t v___x_2198_; uint64_t v_fold_2199_; uint64_t v___x_2200_; uint64_t v___x_2201_; uint64_t v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2195_ = lean_array_get_size(v_x_2187_);
v___x_2196_ = lean_string_hash(v_key_2189_);
v___x_2197_ = 32ULL;
v___x_2198_ = lean_uint64_shift_right(v___x_2196_, v___x_2197_);
v_fold_2199_ = lean_uint64_xor(v___x_2196_, v___x_2198_);
v___x_2200_ = 16ULL;
v___x_2201_ = lean_uint64_shift_right(v_fold_2199_, v___x_2200_);
v___x_2202_ = lean_uint64_xor(v_fold_2199_, v___x_2201_);
v___x_2203_ = lean_uint64_to_usize(v___x_2202_);
v___x_2204_ = lean_usize_of_nat(v___x_2195_);
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_sub(v___x_2204_, v___x_2205_);
v___x_2207_ = lean_usize_land(v___x_2203_, v___x_2206_);
v___x_2208_ = lean_array_uget_borrowed(v_x_2187_, v___x_2207_);
lean_inc(v___x_2208_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 2, v___x_2208_);
v___x_2210_ = v___x_2193_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_key_2189_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_value_2190_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_array_uset(v_x_2187_, v___x_2207_, v___x_2210_);
v_x_2187_ = v___x_2211_;
v_x_2188_ = v_tail_2191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2215_, lean_object* v_source_2216_, lean_object* v_target_2217_){
_start:
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_array_get_size(v_source_2216_);
v___x_2219_ = lean_nat_dec_lt(v_i_2215_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_dec_ref(v_source_2216_);
lean_dec(v_i_2215_);
return v_target_2217_;
}
else
{
lean_object* v_es_2220_; lean_object* v___x_2221_; lean_object* v_source_2222_; lean_object* v_target_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_es_2220_ = lean_array_fget(v_source_2216_, v_i_2215_);
v___x_2221_ = lean_box(0);
v_source_2222_ = lean_array_fset(v_source_2216_, v_i_2215_, v___x_2221_);
v_target_2223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2217_, v_es_2220_);
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_nat_add(v_i_2215_, v___x_2224_);
lean_dec(v_i_2215_);
v_i_2215_ = v___x_2225_;
v_source_2216_ = v_source_2222_;
v_target_2217_ = v_target_2223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(lean_object* v_data_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v_nbuckets_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2228_ = lean_array_get_size(v_data_2227_);
v___x_2229_ = lean_unsigned_to_nat(2u);
v_nbuckets_2230_ = lean_nat_mul(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_mk_array(v_nbuckets_2230_, v___x_2232_);
v___x_2234_ = lean_array_propagate_mark(v_data_2227_, v___x_2233_);
v___x_2235_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(v___x_2231_, v_data_2227_, v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(lean_object* v_a_2236_, lean_object* v_x_2237_){
_start:
{
if (lean_obj_tag(v_x_2237_) == 0)
{
uint8_t v___x_2238_; 
v___x_2238_ = 0;
return v___x_2238_;
}
else
{
lean_object* v_key_2239_; lean_object* v_tail_2240_; uint8_t v___x_2241_; 
v_key_2239_ = lean_ctor_get(v_x_2237_, 0);
v_tail_2240_ = lean_ctor_get(v_x_2237_, 2);
v___x_2241_ = lean_string_dec_eq(v_key_2239_, v_a_2236_);
if (v___x_2241_ == 0)
{
v_x_2237_ = v_tail_2240_;
goto _start;
}
else
{
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg___boxed(lean_object* v_a_2243_, lean_object* v_x_2244_){
_start:
{
uint8_t v_res_2245_; lean_object* v_r_2246_; 
v_res_2245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2243_, v_x_2244_);
lean_dec(v_x_2244_);
lean_dec_ref(v_a_2243_);
v_r_2246_ = lean_box(v_res_2245_);
return v_r_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object* v_m_2247_, lean_object* v_a_2248_, lean_object* v_b_2249_){
_start:
{
lean_object* v_size_2250_; lean_object* v_buckets_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2294_; 
v_size_2250_ = lean_ctor_get(v_m_2247_, 0);
v_buckets_2251_ = lean_ctor_get(v_m_2247_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_m_2247_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2253_ = v_m_2247_;
v_isShared_2254_ = v_isSharedCheck_2294_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_buckets_2251_);
lean_inc(v_size_2250_);
lean_dec(v_m_2247_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2294_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; uint64_t v___x_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v_fold_2259_; uint64_t v___x_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v_bkt_2268_; uint8_t v___x_2269_; 
v___x_2255_ = lean_array_get_size(v_buckets_2251_);
v___x_2256_ = lean_string_hash(v_a_2248_);
v___x_2257_ = 32ULL;
v___x_2258_ = lean_uint64_shift_right(v___x_2256_, v___x_2257_);
v_fold_2259_ = lean_uint64_xor(v___x_2256_, v___x_2258_);
v___x_2260_ = 16ULL;
v___x_2261_ = lean_uint64_shift_right(v_fold_2259_, v___x_2260_);
v___x_2262_ = lean_uint64_xor(v_fold_2259_, v___x_2261_);
v___x_2263_ = lean_uint64_to_usize(v___x_2262_);
v___x_2264_ = lean_usize_of_nat(v___x_2255_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_sub(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_usize_land(v___x_2263_, v___x_2266_);
v_bkt_2268_ = lean_array_uget_borrowed(v_buckets_2251_, v___x_2267_);
v___x_2269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2248_, v_bkt_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v_size_x27_2271_; lean_object* v___x_2272_; lean_object* v_buckets_x27_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2270_ = lean_unsigned_to_nat(1u);
v_size_x27_2271_ = lean_nat_add(v_size_2250_, v___x_2270_);
lean_dec(v_size_2250_);
lean_inc(v_bkt_2268_);
v___x_2272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2248_);
lean_ctor_set(v___x_2272_, 1, v_b_2249_);
lean_ctor_set(v___x_2272_, 2, v_bkt_2268_);
v_buckets_x27_2273_ = lean_array_uset(v_buckets_2251_, v___x_2267_, v___x_2272_);
v___x_2274_ = lean_unsigned_to_nat(4u);
v___x_2275_ = lean_nat_mul(v_size_x27_2271_, v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(3u);
v___x_2277_ = lean_nat_div(v___x_2275_, v___x_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_array_get_size(v_buckets_x27_2273_);
v___x_2279_ = lean_nat_dec_le(v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
if (v___x_2279_ == 0)
{
lean_object* v_val_2280_; lean_object* v___x_2282_; 
v_val_2280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(v_buckets_x27_2273_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v_val_2280_);
lean_ctor_set(v___x_2253_, 0, v_size_x27_2271_);
v___x_2282_ = v___x_2253_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_size_x27_2271_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_val_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_object* v___x_2285_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v_buckets_x27_2273_);
lean_ctor_set(v___x_2253_, 0, v_size_x27_2271_);
v___x_2285_ = v___x_2253_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_size_x27_2271_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_buckets_x27_2273_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
else
{
lean_object* v___x_2287_; lean_object* v_buckets_x27_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
lean_inc(v_bkt_2268_);
v___x_2287_ = lean_box(0);
v_buckets_x27_2288_ = lean_array_uset(v_buckets_2251_, v___x_2267_, v___x_2287_);
v___x_2289_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_2248_, v_b_2249_, v_bkt_2268_);
v___x_2290_ = lean_array_uset(v_buckets_x27_2288_, v___x_2267_, v___x_2289_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v___x_2290_);
v___x_2292_ = v___x_2253_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_size_2250_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(lean_object* v_m_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_buckets_2297_; lean_object* v___x_2298_; uint64_t v___x_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v_fold_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_buckets_2297_ = lean_ctor_get(v_m_2295_, 1);
v___x_2298_ = lean_array_get_size(v_buckets_2297_);
v___x_2299_ = lean_string_hash(v_a_2296_);
v___x_2300_ = 32ULL;
v___x_2301_ = lean_uint64_shift_right(v___x_2299_, v___x_2300_);
v_fold_2302_ = lean_uint64_xor(v___x_2299_, v___x_2301_);
v___x_2303_ = 16ULL;
v___x_2304_ = lean_uint64_shift_right(v_fold_2302_, v___x_2303_);
v___x_2305_ = lean_uint64_xor(v_fold_2302_, v___x_2304_);
v___x_2306_ = lean_uint64_to_usize(v___x_2305_);
v___x_2307_ = lean_usize_of_nat(v___x_2298_);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_sub(v___x_2307_, v___x_2308_);
v___x_2310_ = lean_usize_land(v___x_2306_, v___x_2309_);
v___x_2311_ = lean_array_uget_borrowed(v_buckets_2297_, v___x_2310_);
v___x_2312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2296_, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg___boxed(lean_object* v_m_2313_, lean_object* v_a_2314_){
_start:
{
uint8_t v_res_2315_; lean_object* v_r_2316_; 
v_res_2315_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_2313_, v_a_2314_);
lean_dec_ref(v_a_2314_);
lean_dec_ref(v_m_2313_);
v_r_2316_ = lean_box(v_res_2315_);
return v_r_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_mkTestTask(lean_object* v_label_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_fst_2323_; lean_object* v_snd_2324_; uint8_t v___x_2326_; 
v___x_2319_ = lean_io_promise_new();
v___x_2320_ = l_Lean_Server_Test_Cancel_testTasksRef;
v___x_2321_ = lean_st_ref_take(v___x_2320_);
v___x_2326_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v___x_2321_, v_label_2317_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_inc(v___x_2319_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2319_);
v___x_2328_ = lean_io_promise_result_opt(v___x_2319_);
lean_dec(v___x_2319_);
v___x_2329_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v___x_2321_, v_label_2317_, v___x_2328_);
v_fst_2323_ = v___x_2327_;
v_snd_2324_ = v___x_2329_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2330_; 
lean_dec(v___x_2319_);
lean_dec_ref(v_label_2317_);
v___x_2330_ = lean_box(0);
v_fst_2323_ = v___x_2330_;
v_snd_2324_ = v___x_2321_;
goto v___jp_2322_;
}
v___jp_2322_:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_st_ref_put(v___x_2320_, v_snd_2324_);
return v_fst_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_mkTestTask___boxed(lean_object* v_label_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Server_Test_Cancel_mkTestTask(v_label_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(lean_object* v_00_u03b2_2334_, lean_object* v_m_2335_, lean_object* v_a_2336_){
_start:
{
uint8_t v___x_2337_; 
v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_2335_, v_a_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___boxed(lean_object* v_00_u03b2_2338_, lean_object* v_m_2339_, lean_object* v_a_2340_){
_start:
{
uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_res_2341_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(v_00_u03b2_2338_, v_m_2339_, v_a_2340_);
lean_dec_ref(v_a_2340_);
lean_dec_ref(v_m_2339_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1(lean_object* v_00_u03b2_2343_, lean_object* v_m_2344_, lean_object* v_a_2345_, lean_object* v_b_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_m_2344_, v_a_2345_, v_b_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(lean_object* v_00_u03b2_2348_, lean_object* v_a_2349_, lean_object* v_x_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_2349_, v_x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2352_, lean_object* v_a_2353_, lean_object* v_x_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(v_00_u03b2_2352_, v_a_2353_, v_x_2354_);
lean_dec(v_x_2354_);
lean_dec_ref(v_a_2353_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2(lean_object* v_00_u03b2_2357_, lean_object* v_data_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(v_data_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3(lean_object* v_00_u03b2_2360_, lean_object* v_a_2361_, lean_object* v_b_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_2361_, v_b_2362_, v_x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2365_, lean_object* v_i_2366_, lean_object* v_source_2367_, lean_object* v_target_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(v_i_2366_, v_source_2367_, v_target_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2371_, v_x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(lean_object* v_a_2399_, lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2400_) == 0)
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_box(0);
return v___x_2401_;
}
else
{
lean_object* v_key_2402_; lean_object* v_value_2403_; lean_object* v_tail_2404_; uint8_t v___x_2405_; 
v_key_2402_ = lean_ctor_get(v_x_2400_, 0);
v_value_2403_ = lean_ctor_get(v_x_2400_, 1);
v_tail_2404_ = lean_ctor_get(v_x_2400_, 2);
v___x_2405_ = lean_string_dec_eq(v_key_2402_, v_a_2399_);
if (v___x_2405_ == 0)
{
v_x_2400_ = v_tail_2404_;
goto _start;
}
else
{
lean_object* v___x_2407_; 
lean_inc(v_value_2403_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_value_2403_);
return v___x_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg___boxed(lean_object* v_a_2408_, lean_object* v_x_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_2408_, v_x_2409_);
lean_dec(v_x_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object* v_m_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_buckets_2413_; lean_object* v___x_2414_; uint64_t v___x_2415_; uint64_t v___x_2416_; uint64_t v___x_2417_; uint64_t v_fold_2418_; uint64_t v___x_2419_; uint64_t v___x_2420_; uint64_t v___x_2421_; size_t v___x_2422_; size_t v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_buckets_2413_ = lean_ctor_get(v_m_2411_, 1);
v___x_2414_ = lean_array_get_size(v_buckets_2413_);
v___x_2415_ = lean_string_hash(v_a_2412_);
v___x_2416_ = 32ULL;
v___x_2417_ = lean_uint64_shift_right(v___x_2415_, v___x_2416_);
v_fold_2418_ = lean_uint64_xor(v___x_2415_, v___x_2417_);
v___x_2419_ = 16ULL;
v___x_2420_ = lean_uint64_shift_right(v_fold_2418_, v___x_2419_);
v___x_2421_ = lean_uint64_xor(v_fold_2418_, v___x_2420_);
v___x_2422_ = lean_uint64_to_usize(v___x_2421_);
v___x_2423_ = lean_usize_of_nat(v___x_2414_);
v___x_2424_ = ((size_t)1ULL);
v___x_2425_ = lean_usize_sub(v___x_2423_, v___x_2424_);
v___x_2426_ = lean_usize_land(v___x_2422_, v___x_2425_);
v___x_2427_ = lean_array_uget_borrowed(v_buckets_2413_, v___x_2426_);
v___x_2428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_2412_, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg___boxed(lean_object* v_m_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_m_2429_, v_a_2430_);
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_m_2429_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(lean_object* v_x_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1));
lean_inc(v_x_2435_);
v___x_2439_ = l_Lean_Syntax_isOfKind(v_x_2435_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
lean_dec(v_x_2435_);
v___x_2440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; lean_object* v_label_2442_; lean_object* v_label_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2441_ = lean_unsigned_to_nat(1u);
v_label_2442_ = l_Lean_Syntax_getArg(v_x_2435_, v___x_2441_);
lean_dec(v_x_2435_);
v_label_2443_ = l_Lean_TSyntax_getString(v_label_2442_);
lean_dec(v_label_2442_);
v___x_2444_ = l_Lean_Server_Test_Cancel_testTasksRef;
v___x_2445_ = lean_st_ref_get(v___x_2444_);
v___x_2446_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_2445_, v_label_2443_);
lean_dec(v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_ref_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_ref_2447_ = lean_ctor_get(v_a_2436_, 2);
v___x_2448_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0));
v___x_2449_ = lean_string_append(v___x_2448_, v_label_2443_);
lean_dec_ref(v_label_2443_);
v___x_2450_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2449_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2470_; 
v_a_2459_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2461_ = v___x_2450_;
v_isShared_2462_ = v_isSharedCheck_2470_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2450_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2470_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2463_ = lean_io_error_to_string(v_a_2459_);
v___x_2464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
v___x_2465_ = l_Lean_MessageData_ofFormat(v___x_2464_);
lean_inc(v_ref_2447_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_ref_2447_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2466_);
v___x_2468_ = v___x_2461_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_val_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2513_; 
v_val_2471_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2473_ = v___x_2446_;
v_isShared_2474_ = v_isSharedCheck_2513_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_val_2471_);
lean_dec(v___x_2446_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2513_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_io_wait(v_val_2471_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_ref_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_ref_2476_ = lean_ctor_get(v_a_2436_, 2);
v___x_2477_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1));
v___x_2478_ = lean_string_append(v___x_2477_, v_label_2443_);
lean_dec_ref(v_label_2443_);
v___x_2479_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2));
v___x_2480_ = lean_string_append(v___x_2478_, v___x_2479_);
v___x_2481_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_del_object(v___x_2473_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2503_; 
v_a_2490_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2492_ = v___x_2481_;
v_isShared_2493_ = v_isSharedCheck_2503_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2481_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2503_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_io_error_to_string(v_a_2490_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set_tag(v___x_2473_, 3);
lean_ctor_set(v___x_2473_, 0, v___x_2494_);
v___x_2496_ = v___x_2473_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2497_ = l_Lean_MessageData_ofFormat(v___x_2496_);
lean_inc(v_ref_2476_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_ref_2476_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2498_);
v___x_2500_ = v___x_2492_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
lean_del_object(v___x_2473_);
lean_dec_ref(v_label_2443_);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v___x_2475_, 0);
lean_dec(v_unused_2512_);
v___x_2505_ = v___x_2475_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_dec(v___x_2475_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_box(0);
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___boxed(lean_object* v_x_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_2514_, v_a_2515_);
lean_dec_ref(v_a_2515_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(lean_object* v_x_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_2518_, v_a_2525_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___boxed(lean_object* v_x_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(v_x_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(lean_object* v_00_u03b2_2540_, lean_object* v_m_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_m_2541_, v_a_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___boxed(lean_object* v_00_u03b2_2544_, lean_object* v_m_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(v_00_u03b2_2544_, v_m_2545_, v_a_2546_);
lean_dec_ref(v_a_2546_);
lean_dec_ref(v_m_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(lean_object* v_00_u03b2_2548_, lean_object* v_a_2549_, lean_object* v_x_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_2549_, v_x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2552_, lean_object* v_a_2553_, lean_object* v_x_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(v_00_u03b2_2552_, v_a_2553_, v_x_2554_);
lean_dec(v_x_2554_);
lean_dec_ref(v_a_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_, &l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
v___x_2558_ = lean_st_mk_ref(v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2____boxed(lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_getSyncPromise(lean_object* v_label_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2571_; 
v___x_2564_ = lean_io_promise_new();
v___x_2565_ = l_Lean_Server_Test_Cancel_syncPromisesRef;
v___x_2566_ = lean_st_ref_take(v___x_2565_);
v___x_2571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_2566_, v_label_2562_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_inc(v___x_2564_);
v___x_2572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v___x_2566_, v_label_2562_, v___x_2564_);
v_fst_2568_ = v___x_2564_;
v_snd_2569_ = v___x_2572_;
goto v___jp_2567_;
}
else
{
lean_object* v_val_2573_; 
lean_dec(v___x_2564_);
lean_dec_ref(v_label_2562_);
v_val_2573_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v___x_2571_, 1);
v_fst_2568_ = v_val_2573_;
v_snd_2569_ = v___x_2566_;
goto v___jp_2567_;
}
v___jp_2567_:
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_st_ref_put(v___x_2565_, v_snd_2569_);
return v_fst_2568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_getSyncPromise___boxed(lean_object* v_label_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_resolveSyncPromise(lean_object* v_label_2577_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_2577_);
v___x_2580_ = lean_box(0);
v___x_2581_ = lean_io_promise_resolve(v___x_2580_, v___x_2579_);
lean_dec(v___x_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel_resolveSyncPromise___boxed(lean_object* v_label_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_label_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(lean_object* v_x_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1));
lean_inc(v_x_2606_);
v___x_2610_ = l_Lean_Syntax_isOfKind(v_x_2606_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_dec(v_x_2606_);
v___x_2611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_2611_;
}
else
{
lean_object* v___x_2612_; lean_object* v_label_2613_; lean_object* v_lbl_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2612_ = lean_unsigned_to_nat(1u);
v_label_2613_ = l_Lean_Syntax_getArg(v_x_2606_, v___x_2612_);
lean_dec(v_x_2606_);
v_lbl_2614_ = l_Lean_TSyntax_getString(v_label_2613_);
lean_dec(v_label_2613_);
lean_inc_ref(v_lbl_2614_);
v___x_2615_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_lbl_2614_);
v___x_2616_ = lean_io_promise_result_opt(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2617_ = lean_io_wait(v___x_2616_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_ref_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_ref_2618_ = lean_ctor_get(v_a_2607_, 2);
v___x_2619_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0));
v___x_2620_ = lean_string_append(v___x_2619_, v_lbl_2614_);
lean_dec_ref(v_lbl_2614_);
v___x_2621_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2));
v___x_2622_ = lean_string_append(v___x_2620_, v___x_2621_);
v___x_2623_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2622_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2643_; 
v_a_2632_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2634_ = v___x_2623_;
v_isShared_2635_ = v_isSharedCheck_2643_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2623_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2643_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2636_ = lean_io_error_to_string(v_a_2632_);
v___x_2637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = l_Lean_MessageData_ofFormat(v___x_2637_);
lean_inc(v_ref_2618_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_ref_2618_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2639_);
v___x_2641_ = v___x_2634_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
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
lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_lbl_2614_);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2652_);
v___x_2645_ = v___x_2617_;
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v___x_2617_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = lean_box(0);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2647_);
v___x_2649_ = v___x_2645_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___boxed(lean_object* v_x_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_2653_, v_a_2654_);
lean_dec_ref(v_a_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(lean_object* v_x_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_2657_, v_a_2664_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___boxed(lean_object* v_x_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(v_x_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(lean_object* v___x_2699_, lean_object* v_val_2700_, lean_object* v_a_x3f_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_io_promise_resolve(v___x_2699_, v_val_2700_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0___boxed(lean_object* v___x_2705_, lean_object* v_val_2706_, lean_object* v_a_x3f_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2705_, v_val_2706_, v_a_x3f_2707_);
lean_dec(v_a_x3f_2707_);
lean_dec(v_val_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(lean_object* v___y_2710_){
_start:
{
lean_object* v_toCold_2716_; lean_object* v_cancelTk_x3f_2717_; 
v_toCold_2716_ = lean_ctor_get(v___y_2710_, 0);
v_cancelTk_x3f_2717_ = lean_ctor_get(v_toCold_2716_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2717_) == 1)
{
lean_object* v_val_2718_; uint8_t v___x_2719_; 
v_val_2718_ = lean_ctor_get(v_cancelTk_x3f_2717_, 0);
v___x_2719_ = l_IO_CancelToken_isSet(v_val_2718_);
if (v___x_2719_ == 0)
{
goto v___jp_2712_;
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_dec_ref_known(v___x_2720_, 1);
goto v___jp_2712_;
}
else
{
return v___x_2720_;
}
}
}
else
{
goto v___jp_2712_;
}
v___jp_2712_:
{
uint32_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = 10;
v___x_2714_ = l_IO_sleep(v___x_2713_);
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg___boxed(lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_2721_);
lean_dec_ref(v___y_2721_);
return v_res_2723_;
}
}
static lean_object* _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2725_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11));
v___x_2726_ = lean_unsigned_to_nat(50u);
v___x_2727_ = lean_unsigned_to_nat(302u);
v___x_2728_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0));
v___x_2729_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9));
v___x_2730_ = l_mkPanicMessageWithDecl(v___x_2729_, v___x_2728_, v___x_2727_, v___x_2726_, v___x_2725_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(lean_object* v_x_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1));
lean_inc(v_x_2732_);
v___x_2743_ = l_Lean_Syntax_isOfKind(v_x_2732_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; 
lean_dec(v_x_2732_);
v___x_2744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_2744_;
}
else
{
lean_object* v___x_2745_; lean_object* v_label_2746_; lean_object* v_lbl_2747_; lean_object* v___x_2748_; 
v___x_2745_ = lean_unsigned_to_nat(1u);
v_label_2746_ = l_Lean_Syntax_getArg(v_x_2732_, v___x_2745_);
lean_dec(v_x_2732_);
v_lbl_2747_ = l_Lean_TSyntax_getString(v_label_2746_);
lean_dec(v_label_2746_);
lean_inc_ref(v_lbl_2747_);
v___x_2748_ = l_Lean_Server_Test_Cancel_mkTestTask(v_lbl_2747_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = l_Lean_Server_Test_Cancel_testTasksRef;
v___x_2750_ = lean_st_ref_get(v___x_2749_);
v___x_2751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_2750_, v_lbl_2747_);
lean_dec_ref(v_lbl_2747_);
lean_dec(v___x_2750_);
if (lean_obj_tag(v___x_2751_) == 1)
{
lean_object* v_val_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2761_; 
v_val_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_val_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_io_wait(v_val_2752_);
lean_dec(v___x_2757_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set_tag(v___x_2754_, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2756_);
v___x_2759_ = v___x_2754_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2756_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec(v___x_2751_);
v___x_2762_ = lean_obj_once(&l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1, &l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1_once, _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1);
v___x_2763_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_2762_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
return v___x_2763_;
}
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2813_; 
v_val_2764_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2766_ = v___x_2748_;
v_isShared_2767_ = v_isSharedCheck_2813_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_val_2764_);
lean_dec(v___x_2748_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2813_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_ref_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_ref_2768_ = lean_ctor_get(v_a_2739_, 2);
v___x_2769_ = ((lean_object*)(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2));
lean_inc_ref(v_lbl_2747_);
v___x_2770_ = lean_string_append(v_lbl_2747_, v___x_2769_);
v___x_2771_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v_a_2775_; lean_object* v___x_2788_; 
lean_dec_ref_known(v___x_2771_, 1);
v___x_2772_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_lbl_2747_);
v___x_2773_ = lean_box(0);
v___x_2788_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v_a_2739_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec_ref_known(v___x_2788_, 1);
v_a_2775_ = v___x_2773_;
goto v___jp_2774_;
}
else
{
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v_a_2775_ = v_a_2789_;
goto v___jp_2774_;
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_del_object(v___x_2766_);
v_a_2790_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2791_ = lean_box(0);
v___x_2792_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2773_, v_val_2764_, v___x_2791_);
lean_dec(v_val_2764_);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2792_, 0);
lean_dec(v_unused_2800_);
v___x_2794_ = v___x_2792_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v___x_2792_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 1);
lean_ctor_set(v___x_2794_, 0, v_a_2790_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2790_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
v___jp_2774_:
{
lean_object* v___x_2777_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_a_2775_);
v___x_2777_ = v___x_2766_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2775_);
v___x_2777_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v___x_2778_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_2773_, v_val_2764_, v___x_2777_);
lean_dec_ref(v___x_2777_);
lean_dec(v_val_2764_);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v___x_2778_, 0);
lean_dec(v_unused_2786_);
v___x_2780_ = v___x_2778_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_dec(v___x_2778_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_a_2775_);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2775_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2812_; 
lean_del_object(v___x_2766_);
lean_dec(v_val_2764_);
lean_dec_ref(v_lbl_2747_);
v_a_2801_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2803_ = v___x_2771_;
v_isShared_2804_ = v_isSharedCheck_2812_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2771_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2812_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2805_ = lean_io_error_to_string(v_a_2801_);
v___x_2806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
v___x_2807_ = l_Lean_MessageData_ofFormat(v___x_2806_);
lean_inc(v_ref_2768_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v_ref_2768_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2808_);
v___x_2810_ = v___x_2803_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___boxed(lean_object* v_x_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(v_x_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(lean_object* v_inst_2825_, lean_object* v_a_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_2833_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___boxed(lean_object* v_inst_2837_, lean_object* v_a_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(v_inst_2837_, v_a_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2848_;
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
