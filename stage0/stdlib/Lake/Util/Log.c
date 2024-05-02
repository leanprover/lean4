// Lean compiler output
// Module: Lake.Util.Log
// Imports: Init Lake.Util.Error Lake.Util.EStateT Lean.Data.Json Lean.Message
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
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t, uint8_t);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__16;
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_2259____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__8;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadGetLog_getLogSize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_errorWithLog(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__4;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__11;
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity;
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel;
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instAppend;
LEAN_EXPORT uint8_t l_Lake_Log_hasVisibleEntries(lean_object*, uint8_t);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__12;
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__10;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__19;
lean_object* l_StateT_get___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_logToIO___closed__1;
LEAN_EXPORT uint8_t l_Lake_instInhabitedVerbosity;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__8;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__14;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__2;
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMonadLogTOfPure___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__1;
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___elambda__1___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lake_MonadLog_stdout___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel;
LEAN_EXPORT lean_object* l_Lake_instLTLogLevel;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__3;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__9;
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lake_instReprLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadLogOfMonad___rarg(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__12;
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__2;
static lean_object* l_Lake_instToJsonLogEntry___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__20;
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLTVerbosity;
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_log___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdout___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry;
static lean_object* l_Lake_logToStream___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__21;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lake_instFromJsonLogLevel___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__9;
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instToStringLogEntry___closed__1;
LEAN_EXPORT lean_object* l_Lake_ELogT_log(lean_object*);
static lean_object* l_Lake_Log_instAppend___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadGetLogOfMonadLift___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchFailure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logToIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_shrink___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadLogOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__2;
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError(lean_object*);
static lean_object* l_Lake_instToJsonLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedMonadLogTOfPure(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__8;
LEAN_EXPORT lean_object* l_Lake_Log_filterByVerbosity(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___elambda__1___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_594____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadGetLogOfPure(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprVerbosity___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity;
static lean_object* l_Lake_MonadGetLog_getLogSize___rarg___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__3;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__7;
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_visibleAtVerbosity___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__13;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instEmptyCollection;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadGetLogOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_error___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filterByVerbosity___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_MonadLog_stderr___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__12;
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1;
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_594_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedLogLevel;
static lean_object* l_Lake_instToStringLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadGetLogOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_hasVisibleEntries___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filterByVerbosity___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__17;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__15;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t);
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__15;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filterByVerbosity___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_empty;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logWarning___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchFailure___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__7;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadLogOfMonad(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__4;
static lean_object* l_Lake_logSerialMessage___rarg___closed__1;
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_222_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadLogOfMonad(lean_object*);
static lean_object* l_Lake_instOrdVerbosity___closed__1;
static lean_object* l_Lake_logToStream___closed__2;
static lean_object* l_Lake_logToIO___closed__2;
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadGetLogOfPure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Log_hasVisibleEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713_(uint8_t);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__4;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_instFromJsonLogEntry___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__9;
static lean_object* l_Lake_instInhabitedLogEntry___closed__1;
LEAN_EXPORT lean_object* l_Lake_ELogT_error(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__18;
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LogLevel_visibleAtVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_log___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMonadLogTOfPure___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogT_log(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8;
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__14;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__23;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instToString;
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__13;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__24;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Log_instToString___closed__1;
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Lake_instOrdLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogLevel;
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__2;
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___elambda__1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__5;
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel(uint8_t, uint8_t);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__19;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLogEntry;
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLEVerbosity;
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadGetLog_getLogSize___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO(lean_object*);
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedLogEntry___closed__2;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__4;
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel;
LEAN_EXPORT lean_object* l_Lake_logToIO(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__22;
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054_(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__13;
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__3;
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5;
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___closed__1;
lean_object* l_Lake_EStateT_get___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_Verbosity_noConfusion___rarg___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object*);
lean_object* l_IO_getStderr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadErrorOfMonad___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6;
LEAN_EXPORT lean_object* l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadErrorOfMonad(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__11;
LEAN_EXPORT lean_object* l_Lake_ELogT_errorWithLog___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__5;
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_split___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLELogLevel;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__17;
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__6;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__18;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__6;
LEAN_EXPORT lean_object* l_Lake_Log_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_errorWithLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadGetLogOfMonad(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Log_hasVisibleEntries___spec__1(uint8_t, lean_object*, size_t, size_t);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_222____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348_(uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__2;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11;
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchFailure___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_error___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___elambda__1(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_Verbosity_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_Verbosity_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Verbosity_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Verbosity_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Verbosity_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Verbosity_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_Verbosity_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.Verbosity.quiet", 20);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.Verbosity.normal", 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.Verbosity.verbose", 22);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprVerbosity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprVerbosity___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Verbosity_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_Verbosity_toCtorIdx(x_1);
x_4 = l_Lake_Verbosity_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqVerbosity(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_222_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
switch (x_2) {
case 0:
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
case 1:
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
default: 
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 2;
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_222____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_222_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdVerbosity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_222____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instOrdVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instOrdVerbosity___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instLTVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLEVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_instOrdVerbosity;
x_4 = lean_box(x_1);
x_5 = lean_box(x_2);
x_6 = l_instDecidableRelLe___rarg(x_3, x_4, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instMinVerbosity(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_instOrdVerbosity;
x_4 = lean_box(x_1);
x_5 = lean_box(x_2);
x_6 = l_instDecidableRelLe___rarg(x_3, x_4, x_5);
if (x_6 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instMaxVerbosity(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Lake_instInhabitedVerbosity() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LogLevel_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Verbosity_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LogLevel_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_LogLevel_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lake_instInhabitedLogLevel() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.LogLevel.trace", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.LogLevel.info", 18);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__9;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.LogLevel.warning", 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake.LogLevel.error", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__21;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__4;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__6;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__10;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__12;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
case 2:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__16;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__18;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
default: 
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__22;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__24;
x_26 = l_Repr_addAppParen(x_25, x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprLogLevel___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_1, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 3;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_LogLevel_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_LogLevel_toCtorIdx(x_1);
x_4 = l_Lake_LogLevel_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqLogLevel(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_594_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
}
}
case 2:
{
lean_object* x_10; 
x_10 = lean_box(x_2);
switch (lean_obj_tag(x_10)) {
case 2:
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
case 3:
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
default: 
{
uint8_t x_13; 
lean_dec(x_10);
x_13 = 2;
return x_13;
}
}
}
default: 
{
lean_object* x_14; 
x_14 = lean_box(x_2);
if (lean_obj_tag(x_14) == 3)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 2;
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_594____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_594_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_594____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instOrdLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instOrdLogLevel___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trace", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warning", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__6;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__8;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonLogLevel___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no inductive constructor matched", 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__2;
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__2;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1;
x_3 = l_Except_orElseLazy___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1;
x_9 = l_Except_orElseLazy___rarg(x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1;
x_13 = l_Except_orElseLazy___rarg(x_11, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__3;
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___rarg(x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___rarg(x_11, x_7);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___closed__1;
x_14 = l_Except_orElseLazy___rarg(x_13, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___rarg(x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___rarg(x_11, x_7);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___closed__1;
x_14 = l_Except_orElseLazy___rarg(x_13, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__2;
x_5 = l_Lean_Json_parseTagged(x_1, x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Except_orElseLazy___rarg(x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Except_orElseLazy___rarg(x_10, x_6);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__3;
x_13 = l_Except_orElseLazy___rarg(x_12, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instFromJsonLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonLogLevel___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instLTLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_instLELogLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_instOrdLogLevel;
x_4 = lean_box(x_1);
x_5 = lean_box(x_2);
x_6 = l_instDecidableRelLe___rarg(x_3, x_4, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instMinLogLevel(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_instOrdLogLevel;
x_4 = lean_box(x_1);
x_5 = lean_box(x_2);
x_6 = l_instDecidableRelLe___rarg(x_3, x_4, x_5);
if (x_6 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instMaxLogLevel(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LogLevel_toString(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 2;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 3;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LogLevel_ofMessageSeverity(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instToStringLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LogLevel_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToStringLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToStringLogLevel___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_visibleAtVerbosity(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_4; uint8_t x_5; 
x_4 = 2;
x_5 = l_Lake_instDecidableEqVerbosity(x_2, x_4);
return x_5;
}
case 1:
{
uint8_t x_6; uint8_t x_7; 
x_6 = 0;
x_7 = l_Lake_instDecidableEqVerbosity(x_2, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
default: 
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_visibleAtVerbosity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_LogLevel_visibleAtVerbosity(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_instInhabitedLogEntry___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLogEntry___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(lean_box(0), x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("level", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("message", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054_(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713_(x_2);
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
x_16 = l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____spec__1(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToJsonLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonLogEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752_(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LogEntry", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__1;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__3;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__4;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__7;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__9;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__12;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__14;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2;
x_14 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_2259____spec__1(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unbox(x_12);
lean_dec(x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unbox(x_12);
lean_dec(x_12);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonLogEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = l_Lake_LogLevel_toString(x_2);
x_4 = l_Lake_instInhabitedLogEntry___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_String_trim(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LogEntry_toString(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToStringLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LogEntry_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToStringLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToStringLogEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_logVerbose___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_logVerbose(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_logInfo___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_logInfo(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 2;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_logWarning___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 3;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_logError___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_logToIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warning: ", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_logToIO___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error: ", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logToIO(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
switch (x_4) {
case 0:
{
uint8_t x_5; uint8_t x_6; 
x_5 = 2;
x_6 = l_Lake_instDecidableEqVerbosity(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_String_trim(x_9);
x_11 = l_IO_println___at_Lean_instEval___spec__1(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
case 1:
{
uint8_t x_22; uint8_t x_23; 
x_22 = 0;
x_23 = l_Lake_instDecidableEqVerbosity(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = l_String_trim(x_24);
x_26 = l_IO_println___at_Lean_instEval___spec__1(x_25, x_3);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
}
case 2:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = l_String_trim(x_39);
x_41 = l_Lake_logToIO___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Lake_instInhabitedLogEntry___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_44, x_3);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_45, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
default: 
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = l_String_trim(x_56);
x_58 = l_Lake_logToIO___closed__2;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lake_instInhabitedLogEntry___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_61, x_3);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_62, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set_tag(x_62, 0);
lean_ctor_set(x_62, 0, x_69);
return x_62;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_logToIO(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_logToStream___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trace: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_logToStream___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info: ", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
switch (x_5) {
case 0:
{
uint8_t x_6; uint8_t x_7; 
x_6 = 2;
x_7 = l_Lake_instDecidableEqVerbosity(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_String_trim(x_10);
x_12 = l_Lake_logToStream___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_instInhabitedLogEntry___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_IO_FS_Stream_putStrLn(x_2, x_15, x_4);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
case 1:
{
uint8_t x_27; uint8_t x_28; 
x_27 = 0;
x_28 = l_Lake_instDecidableEqVerbosity(x_3, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = l_String_trim(x_29);
x_31 = l_Lake_logToStream___closed__2;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lake_instInhabitedLogEntry___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_IO_FS_Stream_putStrLn(x_2, x_34, x_4);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
return x_47;
}
}
case 2:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = l_String_trim(x_48);
x_50 = l_Lake_logToIO___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lake_instInhabitedLogEntry___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_IO_FS_Stream_putStrLn(x_2, x_53, x_4);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set_tag(x_54, 0);
lean_ctor_set(x_54, 0, x_61);
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
default: 
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_1, 0);
x_66 = l_String_trim(x_65);
x_67 = l_Lake_logToIO___closed__2;
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = l_Lake_instInhabitedLogEntry___closed__1;
x_70 = lean_string_append(x_68, x_69);
x_71 = l_IO_FS_Stream_putStrLn(x_2, x_70, x_4);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_71, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set_tag(x_71, 0);
lean_ctor_set(x_71, 0, x_78);
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
lean_dec(x_71);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lake_logToStream(x_1, x_2, x_5, x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_logSerialMessage___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":\n", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = l_String_trim(x_4);
lean_dec(x_4);
x_6 = l_String_isEmpty(x_5);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_8 = l_Lake_LogLevel_ofMessageSeverity(x_7);
if (x_6 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_instInhabitedLogEntry___closed__1;
x_13 = lean_string_append(x_12, x_5);
lean_dec(x_5);
x_14 = l_Lake_logSerialMessage___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_String_trim(x_3);
lean_dec(x_3);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_12);
x_19 = l_Lean_mkErrorStringWithPos(x_9, x_10, x_18, x_11);
lean_dec(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_8);
x_21 = lean_apply_1(x_2, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_String_trim(x_3);
lean_dec(x_3);
x_26 = l_Lean_mkErrorStringWithPos(x_22, x_23, x_25, x_24);
lean_dec(x_25);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_8);
x_28 = lean_apply_1(x_2, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_logSerialMessage___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___elambda__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___elambda__1___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLog_nop___elambda__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___elambda__1___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_instInhabitedOfPure___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___elambda__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_logToIO___boxed), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_io___elambda__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_MonadLog_io___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_io___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_MonadLog_io___elambda__1___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lake_MonadLog_io___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lake_MonadLog_stream___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_logToStream(x_1, x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_MonadLog_stdout___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_getStdout___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lake_MonadLog_stdout___rarg___closed__1;
x_7 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_MonadLog_stdout___rarg___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_MonadLog_stdout___rarg(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_MonadLog_stderr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_getStderr___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lake_MonadLog_stderr___rarg___closed__1;
x_7 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_stderr___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_MonadLog_stderr___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedMonadLogTOfPure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedMonadLogTOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instInhabitedMonadLogTOfPure___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedMonadLogTOfPure___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instInhabitedMonadLogTOfPure___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_3, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
x_9 = lean_alloc_closure((void*)(l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadLogMonadLogTOfMonadOfMonadLiftT___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lake_MonadLogT_adaptMethods___rarg), 3, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_MonadLogT_adaptMethods(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___elambda__1___rarg___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_MonadLogT_ignoreLog___rarg), 2, 0);
return x_4;
}
}
static lean_object* _init_l_Lake_Log_empty() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Log_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Log_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Log_size(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_append___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Log_instAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Log_append), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_instAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Log_instAppend___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_shrink(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_shrink___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_shrink(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_extract___rarg(x_1, x_3, x_2);
x_5 = l_Array_shrink___rarg(x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_split(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_LogEntry_toString(x_6);
lean_dec(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lake_instInhabitedLogEntry___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lake_instInhabitedLogEntry___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Lake_instInhabitedLogEntry___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Log_toString(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Log_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Log_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Log_instToString___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_4, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg(x_1, x_2, x_3, x_16, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Log_replay___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_11;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1(x_1, x_2, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_filter(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filterByVerbosity___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_9 = l_Lake_LogLevel_visibleAtVerbosity(x_8, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_11;
x_5 = x_13;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filterByVerbosity(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Log_filterByVerbosity___spec__1(x_2, x_1, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filterByVerbosity___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Log_filterByVerbosity___spec__1(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filterByVerbosity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lake_Log_filterByVerbosity(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1(x_1, x_2, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Log_any(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Log_hasVisibleEntries___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_8 = l_Lake_LogLevel_visibleAtVerbosity(x_7, x_1);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_hasVisibleEntries(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lake_Log_hasVisibleEntries___spec__1(x_2, x_1, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Log_hasVisibleEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_Lake_Log_hasVisibleEntries___spec__1(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasVisibleEntries___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lake_Log_hasVisibleEntries(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_MonadGetLog_getLogSize___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_size___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadGetLog_getLogSize___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_MonadGetLog_getLogSize___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadGetLog_getLogSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadGetLog_getLogSize___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadGetLogOfMonadLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadGetLogOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadGetLogOfMonadLift___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadGetLogOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_StateT_get___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadGetLogOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LogT_instMonadGetLogOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_log___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_push(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_log(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LogT_log___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadLogOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LogT_log___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_instMonadLogOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LogT_instMonadLogOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadGetLogOfPure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_EStateT_get___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadGetLogOfPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELogT_instMonadGetLogOfPure___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_log___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_push(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_log(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELogT_log___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadLogOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELogT_log___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadLogOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELogT_instMonadLogOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_errorWithLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_2);
x_8 = lean_apply_2(x_7, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_3, 0, x_2);
x_18 = lean_apply_2(x_17, lean_box(0), x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_errorWithLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_ELogT_errorWithLog___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_errorWithLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_ELogT_errorWithLog___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_error___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_1);
x_12 = lean_apply_2(x_2, lean_box(0), x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_error___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = 3;
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
x_6 = lean_array_get_size(x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_push(x_3, x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_inc(x_9);
x_13 = lean_apply_2(x_9, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_ELogT_error___rarg___lambda__1), 3, 2);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_9);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_error(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_error___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadErrorOfMonad___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = 3;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
x_7 = lean_array_get_size(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_push(x_4, x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_inc(x_10);
x_14 = lean_apply_2(x_10, lean_box(0), x_13);
x_15 = lean_alloc_closure((void*)(l_Lake_ELogT_error___rarg___lambda__1), 3, 2);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_10);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_instMonadErrorOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELogT_instMonadErrorOfMonad___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_array_get_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_5);
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_16, x_12);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_9, x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_22, x_12);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_26 = lean_box(0);
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg(x_2, x_3, x_6, x_24, x_25, x_26);
x_28 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_27, x_12);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 4);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_array_get_size(x_29);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
x_35 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_35, 0, x_1);
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_3);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = lean_apply_2(x_37, lean_box(0), x_38);
x_40 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_39, x_35);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_32, x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_3);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
x_46 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_45, x_35);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg(x_2, x_3, x_29, x_47, x_48, x_49);
x_51 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_50, x_35);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___rarg___lambda__3), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_ELogT_replayLog___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ELogT_replayLog___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchFailure___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_extract___rarg(x_11, x_12, x_10);
x_14 = l_Array_shrink___rarg(x_11, x_10);
lean_dec(x_10);
x_15 = lean_apply_2(x_2, x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchFailure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_ELogT_catchFailure___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchFailure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_catchFailure___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1;
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lake_ELogT_captureLog___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_captureLog___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ELogT_captureLog___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_io_error_to_string(x_13);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_array_get_size(x_2);
x_18 = lean_array_push(x_2, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_io_error_to_string(x_20);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_get_size(x_2);
x_26 = lean_array_push(x_2, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftIOLogIO___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EStateT(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EStateT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Verbosity_noConfusion___rarg___closed__1 = _init_l_Lake_Verbosity_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lake_Verbosity_noConfusion___rarg___closed__1);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__1);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__2);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__3);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__4);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__5);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__6);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__7);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__8);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__9 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__9();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__9);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__10);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__11 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__11();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__11);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__12 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__12();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__12);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__13 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__13();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__13);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__14 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__14();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__14);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__15 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__15();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__15);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__16);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__17 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__17();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__17);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__18 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__18();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__18);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__19 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__19();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__19);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__20 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__20();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_8____closed__20);
l_Lake_instReprVerbosity___closed__1 = _init_l_Lake_instReprVerbosity___closed__1();
lean_mark_persistent(l_Lake_instReprVerbosity___closed__1);
l_Lake_instReprVerbosity = _init_l_Lake_instReprVerbosity();
lean_mark_persistent(l_Lake_instReprVerbosity);
l_Lake_instOrdVerbosity___closed__1 = _init_l_Lake_instOrdVerbosity___closed__1();
lean_mark_persistent(l_Lake_instOrdVerbosity___closed__1);
l_Lake_instOrdVerbosity = _init_l_Lake_instOrdVerbosity();
lean_mark_persistent(l_Lake_instOrdVerbosity);
l_Lake_instLTVerbosity = _init_l_Lake_instLTVerbosity();
lean_mark_persistent(l_Lake_instLTVerbosity);
l_Lake_instLEVerbosity = _init_l_Lake_instLEVerbosity();
lean_mark_persistent(l_Lake_instLEVerbosity);
l_Lake_instInhabitedVerbosity = _init_l_Lake_instInhabitedVerbosity();
l_Lake_instInhabitedLogLevel = _init_l_Lake_instInhabitedLogLevel();
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__1);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__2);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__3);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__4);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__5);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__6);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__7);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__8);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__9 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__9();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__9);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__10 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__10();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__10);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__11 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__11();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__11);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__12 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__12();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__12);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__13 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__13();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__13);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__14);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__15 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__15();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__15);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__16 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__16();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__16);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__17 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__17();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__17);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__18 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__18();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__18);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__19 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__19();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__19);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__20);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__21 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__21();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__21);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__22 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__22();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__22);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__23 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__23();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__23);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__24 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__24();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_348____closed__24);
l_Lake_instReprLogLevel___closed__1 = _init_l_Lake_instReprLogLevel___closed__1();
lean_mark_persistent(l_Lake_instReprLogLevel___closed__1);
l_Lake_instReprLogLevel = _init_l_Lake_instReprLogLevel();
lean_mark_persistent(l_Lake_instReprLogLevel);
l_Lake_instOrdLogLevel___closed__1 = _init_l_Lake_instOrdLogLevel___closed__1();
lean_mark_persistent(l_Lake_instOrdLogLevel___closed__1);
l_Lake_instOrdLogLevel = _init_l_Lake_instOrdLogLevel();
lean_mark_persistent(l_Lake_instOrdLogLevel);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__1);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__2);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__3);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__4);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__5);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__6);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__7);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_713____closed__8);
l_Lake_instToJsonLogLevel___closed__1 = _init_l_Lake_instToJsonLogLevel___closed__1();
lean_mark_persistent(l_Lake_instToJsonLogLevel___closed__1);
l_Lake_instToJsonLogLevel = _init_l_Lake_instToJsonLogLevel();
lean_mark_persistent(l_Lake_instToJsonLogLevel);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__1___closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__3 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__2___closed__3);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__3___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____lambda__4___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_752____closed__3);
l_Lake_instFromJsonLogLevel___closed__1 = _init_l_Lake_instFromJsonLogLevel___closed__1();
lean_mark_persistent(l_Lake_instFromJsonLogLevel___closed__1);
l_Lake_instFromJsonLogLevel = _init_l_Lake_instFromJsonLogLevel();
lean_mark_persistent(l_Lake_instFromJsonLogLevel);
l_Lake_instLTLogLevel = _init_l_Lake_instLTLogLevel();
lean_mark_persistent(l_Lake_instLTLogLevel);
l_Lake_instLELogLevel = _init_l_Lake_instLELogLevel();
lean_mark_persistent(l_Lake_instLELogLevel);
l_Lake_instToStringLogLevel___closed__1 = _init_l_Lake_instToStringLogLevel___closed__1();
lean_mark_persistent(l_Lake_instToStringLogLevel___closed__1);
l_Lake_instToStringLogLevel = _init_l_Lake_instToStringLogLevel();
lean_mark_persistent(l_Lake_instToStringLogLevel);
l_Lake_instInhabitedLogEntry___closed__1 = _init_l_Lake_instInhabitedLogEntry___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLogEntry___closed__1);
l_Lake_instInhabitedLogEntry___closed__2 = _init_l_Lake_instInhabitedLogEntry___closed__2();
lean_mark_persistent(l_Lake_instInhabitedLogEntry___closed__2);
l_Lake_instInhabitedLogEntry = _init_l_Lake_instInhabitedLogEntry();
lean_mark_persistent(l_Lake_instInhabitedLogEntry);
l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__1);
l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____closed__2);
l_Lake_instToJsonLogEntry___closed__1 = _init_l_Lake_instToJsonLogEntry___closed__1();
lean_mark_persistent(l_Lake_instToJsonLogEntry___closed__1);
l_Lake_instToJsonLogEntry = _init_l_Lake_instToJsonLogEntry();
lean_mark_persistent(l_Lake_instToJsonLogEntry);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__3);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__4);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__5);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__6);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__7);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__8);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__9 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__9();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__9);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__10);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__11);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__12 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__12();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__12);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__13 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__13();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__13);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__14 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__14();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__14);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1100____closed__15);
l_Lake_instFromJsonLogEntry___closed__1 = _init_l_Lake_instFromJsonLogEntry___closed__1();
lean_mark_persistent(l_Lake_instFromJsonLogEntry___closed__1);
l_Lake_instFromJsonLogEntry = _init_l_Lake_instFromJsonLogEntry();
lean_mark_persistent(l_Lake_instFromJsonLogEntry);
l_Lake_instToStringLogEntry___closed__1 = _init_l_Lake_instToStringLogEntry___closed__1();
lean_mark_persistent(l_Lake_instToStringLogEntry___closed__1);
l_Lake_instToStringLogEntry = _init_l_Lake_instToStringLogEntry();
lean_mark_persistent(l_Lake_instToStringLogEntry);
l_Lake_logToIO___closed__1 = _init_l_Lake_logToIO___closed__1();
lean_mark_persistent(l_Lake_logToIO___closed__1);
l_Lake_logToIO___closed__2 = _init_l_Lake_logToIO___closed__2();
lean_mark_persistent(l_Lake_logToIO___closed__2);
l_Lake_logToStream___closed__1 = _init_l_Lake_logToStream___closed__1();
lean_mark_persistent(l_Lake_logToStream___closed__1);
l_Lake_logToStream___closed__2 = _init_l_Lake_logToStream___closed__2();
lean_mark_persistent(l_Lake_logToStream___closed__2);
l_Lake_logSerialMessage___rarg___closed__1 = _init_l_Lake_logSerialMessage___rarg___closed__1();
lean_mark_persistent(l_Lake_logSerialMessage___rarg___closed__1);
l_Lake_MonadLog_stdout___rarg___closed__1 = _init_l_Lake_MonadLog_stdout___rarg___closed__1();
lean_mark_persistent(l_Lake_MonadLog_stdout___rarg___closed__1);
l_Lake_MonadLog_stderr___rarg___closed__1 = _init_l_Lake_MonadLog_stderr___rarg___closed__1();
lean_mark_persistent(l_Lake_MonadLog_stderr___rarg___closed__1);
l_Lake_Log_empty = _init_l_Lake_Log_empty();
lean_mark_persistent(l_Lake_Log_empty);
l_Lake_Log_instEmptyCollection = _init_l_Lake_Log_instEmptyCollection();
lean_mark_persistent(l_Lake_Log_instEmptyCollection);
l_Lake_Log_instAppend___closed__1 = _init_l_Lake_Log_instAppend___closed__1();
lean_mark_persistent(l_Lake_Log_instAppend___closed__1);
l_Lake_Log_instAppend = _init_l_Lake_Log_instAppend();
lean_mark_persistent(l_Lake_Log_instAppend);
l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1);
l_Lake_Log_instToString___closed__1 = _init_l_Lake_Log_instToString___closed__1();
lean_mark_persistent(l_Lake_Log_instToString___closed__1);
l_Lake_Log_instToString = _init_l_Lake_Log_instToString();
lean_mark_persistent(l_Lake_Log_instToString);
l_Lake_MonadGetLog_getLogSize___rarg___closed__1 = _init_l_Lake_MonadGetLog_getLogSize___rarg___closed__1();
lean_mark_persistent(l_Lake_MonadGetLog_getLogSize___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
