// Lean compiler output
// Module: Lake.Util.Log
// Imports: Lake.Util.Error Lake.Util.EStateT Lake.Util.Lift Lean.Data.Json Lean.Message
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
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__5;
LEAN_EXPORT lean_object* l_Lake_LogT_run___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876_(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity;
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel;
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object*);
lean_object* l_Lake_EResult_toProd_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__22;
LEAN_EXPORT uint8_t l_Lake_instOrdPos(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__9;
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instAppend;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__11;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2;
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454_(lean_object*);
static lean_object* l_Lake_ELogT_run_x3f_x27___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___rarg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedVerbosity;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__12;
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__24;
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object*);
static lean_object* l_Lake_takeLog___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__10;
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel;
LEAN_EXPORT lean_object* l_Lake_instLTLogLevel;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2;
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instInhabitedPos;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__17;
LEAN_EXPORT lean_object* l_Lake_ELogT_run___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1;
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__3;
LEAN_EXPORT lean_object* l_Lake_instMaxPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__15;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14;
static lean_object* l_Lake_instReprLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_756____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object*);
static lean_object* l_Lake_instToJsonLogEntry___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__6;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5;
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLTVerbosity;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_maxLv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose___rarg(lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at___private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173____spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_getLogPos___rarg___closed__1;
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_225____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lake_instFromJsonLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_225_(uint8_t, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__18;
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ansiColor___closed__3;
static lean_object* l_Lake_Log_instAppend___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonLog___closed__1;
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logToIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_3138____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError(lean_object*);
static lean_object* l_Lake_instToJsonLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLog;
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__20;
LEAN_EXPORT lean_object* l_Lake_instLTPos;
LEAN_EXPORT lean_object* l_Lake_instMinPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__15;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16;
static lean_object* l_Lake_instReprVerbosity___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogELogTOfMonad___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity;
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__21;
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_error___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__13;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__15;
LEAN_EXPORT lean_object* l_Lake_Log_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__8;
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object*);
static lean_object* l_Lake_ELogT_toLogT_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog(lean_object*);
lean_object* l_String_mapAux___at_String_toLower___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__18;
LEAN_EXPORT lean_object* l_Lake_getLog___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object*);
static lean_object* l_Lake_Ansi_chalk___closed__3;
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__23;
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogIO_toBaseIO_replay___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO_replay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__7;
LEAN_EXPORT lean_object* l_Lake_instLEPos;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__9;
LEAN_EXPORT uint8_t l_Lake_instInhabitedLogLevel;
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Lake_instToStringLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__10;
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__7;
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t);
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_empty;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logWarning___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO_replay___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__1;
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_Log_decEqPos____x40_Lake_Util_Log___hyg_2718____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__9;
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__2;
LEAN_EXPORT lean_object* l_Lake_ELog_failure___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_756_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____spec__1(lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogIO_toBaseIO_replay___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogT_run_x27___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogEntry_toString___closed__1;
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__6;
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__3;
static lean_object* l_Lake_logSerialMessage___rarg___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8;
static lean_object* l_Lake_instOrdVerbosity___closed__1;
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogLogTOfMonad___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__12;
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_failure___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lake_EResult_toProd___rarg(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__2;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__2;
lean_object* l_Lake_EResult_toExcept___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1(lean_object*);
static lean_object* l_Lake_instFromJsonLogEntry___closed__1;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__16;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object*);
static lean_object* l_Lake_instInhabitedLogEntry___closed__1;
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__6;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__19;
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonLog(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__17;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instToString;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__13;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11;
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io(lean_object*);
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ansiColor___closed__1;
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object*);
static lean_object* l_Lake_Log_instToString___closed__1;
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___rarg(lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_replay___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t);
static lean_object* l_Lake_instOrdLogLevel___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_Ansi_chalk___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogLevel;
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___boxed(lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedLog___closed__1;
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10_(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel(uint8_t, uint8_t);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__4;
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__19;
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLogEntry;
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_instLEVerbosity;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Ansi_chalk___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object*);
static lean_object* l_Lake_LogLevel_ansiColor___closed__2;
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO(lean_object*);
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_withLoggedIO___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__14;
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_filter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedLogEntry___closed__2;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel;
LEAN_EXPORT lean_object* l_Lake_logToIO(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_LogEntry_toString___closed__2;
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ELogT_toLogT___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__3;
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__3;
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogELogTOfMonad___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOfNatPos;
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3;
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20;
static lean_object* l_Lake_ELogT_run_x27___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_Log_decEqPos____x40_Lake_Util_Log___hyg_2718_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO(lean_object*);
static lean_object* l_Lake_Verbosity_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__8;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_Log_maxLv___spec__1(lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_size___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonLog___closed__2;
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry;
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__14;
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__2;
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__8;
static lean_object* l_Lake_logSerialMessage___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLELogLevel;
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___rarg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Verbosity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509_(uint8_t, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__13;
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__11;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7;
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Log_any___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__4;
static lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EResult_result_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogLogTOfMonad___spec__1(lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__4;
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
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Verbosity.quiet", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Verbosity.normal", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Verbosity.verbose", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10_(uint8_t x_1, lean_object* x_2) {
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
x_5 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__8;
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
x_11 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__14;
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
x_17 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprVerbosity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____boxed), 2, 0);
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
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_225_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_225____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_225_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdVerbosity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_ordVerbosity____x40_Lake_Util_Log___hyg_225____boxed), 2, 0);
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
x_6 = l_Ord_instDecidableRelLe___rarg(x_3, x_4, x_5);
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
x_6 = l_Ord_instDecidableRelLe___rarg(x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lake_AnsiMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_AnsiMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Verbosity_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_AnsiMode_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_AnsiMode_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
case 1:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
default: 
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_AnsiMode_isEnabled(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Ansi_chalk___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\x1b[1;", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Ansi_chalk___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("m", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Ansi_chalk___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\x1b[m", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lake_Ansi_chalk___closed__1;
x_4 = lean_string_append(x_3, x_1);
x_5 = l_Lake_Ansi_chalk___closed__2;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_string_append(x_6, x_2);
x_8 = l_Lake_Ansi_chalk___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Ansi_chalk(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_get_stdout(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_get_stderr(x_2);
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OutStream_get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_stream_of_handle(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
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
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.trace", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.info", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__9;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.warning", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.error", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__21;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6;
x_2 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509_(uint8_t x_1, lean_object* x_2) {
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
x_5 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__4;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__6;
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
x_11 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__10;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__12;
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
x_17 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__16;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__18;
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
x_23 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__22;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__24;
x_26 = l_Repr_addAppParen(x_25, x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____boxed), 2, 0);
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
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_756_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_756____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_756_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_ordLogLevel____x40_Lake_Util_Log___hyg_756____boxed), 2, 0);
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
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__6;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__8;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____boxed), 1, 0);
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
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__2;
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__2() {
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
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__2;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1;
x_3 = l_Except_orElseLazy___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1;
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
x_12 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1;
x_13 = l_Except_orElseLazy___rarg(x_11, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__3;
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___closed__1() {
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3;
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___boxed), 3, 2);
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
x_13 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___closed__1;
x_14 = l_Except_orElseLazy___rarg(x_13, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___closed__1() {
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1;
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___boxed), 3, 2);
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
x_13 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___closed__1;
x_14 = l_Except_orElseLazy___rarg(x_13, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__3() {
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Json_parseTagged(x_1, x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___boxed), 3, 2);
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
x_12 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__3;
x_13 = l_Except_orElseLazy___rarg(x_12, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instFromJsonLogLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921_), 1, 0);
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
x_6 = l_Ord_instDecidableRelLe___rarg(x_3, x_4, x_5);
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
x_6 = l_Ord_instDecidableRelLe___rarg(x_3, x_4, x_5);
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
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 2:
{
uint32_t x_3; 
x_3 = 9888;
return x_3;
}
case 3:
{
uint32_t x_4; 
x_4 = 10006;
return x_4;
}
default: 
{
uint32_t x_5; 
lean_dec(x_2);
x_5 = 8505;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LogLevel_icon(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_LogLevel_ansiColor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("34", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ansiColor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("33", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ansiColor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("31", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; 
x_3 = l_Lake_LogLevel_ansiColor___closed__2;
return x_3;
}
case 3:
{
lean_object* x_4; 
x_4 = l_Lake_LogLevel_ansiColor___closed__3;
return x_4;
}
default: 
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lake_LogLevel_ansiColor___closed__1;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LogLevel_ansiColor(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("information", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warn", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__3() {
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
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__4() {
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
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__5() {
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
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__6() {
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
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_String_mapAux___at_String_toLower___spec__1(x_2, x_1);
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3;
x_7 = lean_string_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_LogLevel_ofString_x3f___closed__1;
x_9 = lean_string_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_LogLevel_ofString_x3f___closed__2;
x_11 = lean_string_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5;
x_13 = lean_string_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7;
x_15 = lean_string_dec_eq(x_3, x_14);
lean_dec(x_3);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lake_LogLevel_ofString_x3f___closed__3;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = l_Lake_LogLevel_ofString_x3f___closed__4;
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_3);
x_19 = l_Lake_LogLevel_ofString_x3f___closed__4;
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_3);
x_20 = l_Lake_LogLevel_ofString_x3f___closed__5;
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = l_Lake_LogLevel_ofString_x3f___closed__5;
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = l_Lake_LogLevel_ofString_x3f___closed__6;
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7;
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
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 3:
{
uint8_t x_4; 
x_4 = 2;
return x_4;
}
default: 
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LogLevel_toMessageSeverity(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_2; 
x_2 = 2;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_Verbosity_minLogLv(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
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
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("level", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402_(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876_(x_2);
x_4 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1;
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
x_10 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2;
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
x_15 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_16 = l_List_flatMapTR_go___at___private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173____spec__1(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToJsonLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921_(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LogEntry", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__1;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__3;
x_2 = 1;
x_3 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__5;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__9() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__8;
x_2 = 1;
x_3 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__10;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__13;
x_2 = 1;
x_3 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__14;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__15;
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12;
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
x_9 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12;
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
x_13 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2;
x_14 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Message_0__Lean_fromJsonBaseMessage____x40_Lean_Message___hyg_3138____spec__1(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16;
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
x_20 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454_), 1, 0);
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
static lean_object* _init_l_Lake_LogEntry_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LogEntry_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = l_Lake_LogLevel_toString(x_3);
x_5 = l_Lake_instInhabitedLogEntry___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lake_LogLevel_ansiColor(x_12);
x_15 = l_Lake_LogLevel_toString(x_12);
x_16 = l_Lake_instInhabitedLogEntry___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lake_LogEntry_toString___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lake_Ansi_chalk(x_14, x_19);
lean_dec(x_19);
lean_dec(x_14);
x_21 = lean_string_append(x_16, x_20);
lean_dec(x_20);
x_22 = l_Lake_LogEntry_toString___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_13);
x_25 = lean_string_append(x_24, x_16);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lake_LogEntry_toString(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = l_Lake_LogEntry_toString(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToStringLogEntry(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
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
static lean_object* _init_l_Lake_logSerialMessage___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_logSerialMessage___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = l_Lake_logSerialMessage___rarg___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Substring_takeWhileAux(x_4, x_5, x_6, x_7);
x_9 = l_Substring_takeRightWhileAux(x_4, x_8, x_6, x_5);
x_10 = lean_string_utf8_extract(x_4, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_nat_dec_eq(x_11, x_7);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 1);
x_14 = l_Lake_LogLevel_ofMessageSeverity(x_13);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_box(0);
if (x_12 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = l_Lake_instInhabitedLogEntry___closed__1;
x_19 = lean_string_append(x_18, x_10);
lean_dec(x_10);
x_20 = l_Lake_logSerialMessage___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_string_utf8_byte_size(x_22);
x_24 = l_Substring_takeWhileAux(x_22, x_23, x_6, x_7);
x_25 = l_Substring_takeRightWhileAux(x_22, x_24, x_6, x_23);
x_26 = lean_string_utf8_extract(x_22, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
x_27 = lean_string_append(x_21, x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_27, x_18);
x_29 = l_Lean_mkErrorStringWithPos(x_15, x_16, x_28, x_17);
lean_dec(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_14);
x_31 = lean_apply_1(x_2, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
lean_dec(x_3);
x_33 = lean_string_utf8_byte_size(x_32);
x_34 = l_Substring_takeWhileAux(x_32, x_33, x_6, x_7);
x_35 = l_Substring_takeRightWhileAux(x_32, x_34, x_6, x_33);
x_36 = lean_string_utf8_extract(x_32, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_37 = l_Lean_mkErrorStringWithPos(x_15, x_16, x_36, x_17);
lean_dec(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_14);
x_39 = lean_apply_1(x_2, x_38);
return x_39;
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
LEAN_EXPORT lean_object* l_Lake_logToIO(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_box(x_4);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lake_instOrdLogLevel;
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_box(x_2);
x_10 = l_Ord_instDecidableRelLe___rarg(x_6, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_string_utf8_byte_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_13, x_14, x_15);
x_17 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_13, x_16, x_14);
x_18 = lean_string_utf8_extract(x_13, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_18, x_3);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
case 1:
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = l_Lake_instOrdLogLevel;
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_box(x_2);
x_34 = l_Ord_instDecidableRelLe___rarg(x_30, x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_string_utf8_byte_size(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_37, x_38, x_39);
x_41 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_37, x_40, x_38);
x_42 = lean_string_utf8_extract(x_37, x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
x_43 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_42, x_3);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set_tag(x_43, 0);
lean_ctor_set(x_43, 0, x_50);
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
default: 
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_5);
x_54 = 0;
x_55 = l_Lake_LogEntry_toString(x_1, x_54);
x_56 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_55, x_3);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set_tag(x_56, 0);
lean_ctor_set(x_56, 0, x_63);
return x_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
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
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = l_Lake_instOrdLogLevel;
x_8 = lean_box(x_3);
x_9 = lean_box(x_6);
x_10 = l_Ord_instDecidableRelLe___rarg(x_7, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lake_LogEntry_toString(x_1, x_4);
x_14 = l_IO_FS_Stream_putStrLn(x_2, x_13, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_logToStream(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLog_nop___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_instInhabitedOfPure___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLog_instInhabitedOfPure___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_io(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_io___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_io___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_MonadLog_io___rarg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(x_3);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_MonadLog_stream___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 3;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLog_error___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_OutStream_get(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unbox(x_10);
lean_dec(x_10);
x_13 = l_Lake_logToStream(x_2, x_7, x_3, x_12, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_OutStream_logEntry(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(x_3);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_OutStream_logger___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_OutStream_logger___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_box(x_2);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_MonadLog_stdout___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(1);
x_6 = lean_box(x_2);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_stderr___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_MonadLog_stderr___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(x_2);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_logToStream___boxed), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_OutStream_get(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_OutStream_getLogger___rarg___lambda__1(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_OutStream_getLogger___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_MonadLogT_instInhabitedOfPure___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_3, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___rarg), 4, 0);
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
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLogT_ignoreLog___rarg___lambda__1___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLogT_ignoreLog___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLog___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLog___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402_(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454_(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_instFromJsonLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
x_4 = l_Lake_instFromJsonLog___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lake_instFromJsonLog___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_1, x_9);
x_11 = l_Lake_instFromJsonLog___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_instFromJsonLog___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 4:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(x_17, x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
default: 
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(80u);
lean_inc(x_1);
x_27 = l_Lean_Json_pretty(x_1, x_26);
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 0);
lean_dec(x_29);
x_30 = l_Lake_instFromJsonLog___closed__1;
x_31 = lean_string_append(x_30, x_27);
lean_dec(x_27);
x_32 = l_Lake_instFromJsonLog___closed__2;
x_33 = lean_string_append(x_31, x_32);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_34 = l_Lake_instFromJsonLog___closed__1;
x_35 = lean_string_append(x_34, x_27);
lean_dec(x_27);
x_36 = l_Lake_instFromJsonLog___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Log_instInhabitedPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Log_0__Lake_Log_decEqPos____x40_Lake_Util_Log___hyg_2718_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_Log_decEqPos____x40_Lake_Util_Log___hyg_2718____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Util_Log_0__Lake_Log_decEqPos____x40_Lake_Util_Log___hyg_2718_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Log_instDecidableEqPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instOfNatPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instOrdPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instLTPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableRelPosLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instLEPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableRelPosLe(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMinPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMaxPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Log_empty() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Log_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
return x_1;
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
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
x_5 = l_instDecidableNot___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Log_hasEntries(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Log_endPos(x_1);
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
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_append(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Log_instAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Log_append___boxed), 2, 0);
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
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_extract___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Log_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_dropFrom(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_extract___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_takeFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = l_Array_shrink___rarg(x_1, x_2);
x_4 = lean_array_get_size(x_1);
x_5 = l_Array_extract___rarg(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 0;
x_8 = l_Lake_LogEntry_toString(x_6, x_7);
lean_dec(x_6);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Log_toString___spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
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
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
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
x_8 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
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
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_Log_maxLv___spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_dec(x_6);
x_8 = l_Lake_instOrdLogLevel;
x_9 = lean_box(x_4);
x_10 = lean_box(x_7);
x_11 = l_Ord_instDecidableRelLe___rarg(x_8, x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
if (x_11 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
x_2 = x_13;
x_4 = x_7;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = 0;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_Log_maxLv___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Log_maxLv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_Log_maxLv___spec__1(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Log_maxLv(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_array_push(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___rarg___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_ofMonadState___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLog___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLog___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getLogPos___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_size___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lake_getLogPos___rarg___closed__1;
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLogPos___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_takeLog___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_takeLog___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lake_takeLog___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_takeLog___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
lean_inc(x_1);
x_4 = l_Array_extract___rarg(x_2, x_1, x_3);
lean_dec(x_3);
x_5 = l_Array_shrink___rarg(x_2, x_1);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_takeLogFrom___rarg___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_takeLogFrom___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Array_shrink___rarg(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_dropLogFrom___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_dropLogFrom___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_dropLogFrom___rarg___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_get_size(x_3);
x_6 = l_Array_extract___rarg(x_3, x_2, x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_extractLog___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_extractLog___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lake_getLogPos___rarg___closed__1;
lean_inc(x_8);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_8);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_extractLog___rarg___lambda__3), 5, 4);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_extractLog___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_extractLog___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_extractLog___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_4);
x_7 = l_Array_extract___rarg(x_4, x_2, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_withExtractLog___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_withExtractLog___rarg___lambda__2), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lake_getLogPos___rarg___closed__1;
lean_inc(x_8);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_8);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_withExtractLog___rarg___lambda__3), 5, 4);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_withExtractLog___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_withExtractLog___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, lean_box(0), x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lake_getLogPos___rarg___closed__1;
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___rarg___lambda__2), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_4);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_withLogErrorPos___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_closure((void*)(l_Lake_errorWithLog___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_apply_3(x_7, lean_box(0), x_3, x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lake_getLogPos___rarg___closed__1;
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_errorWithLog___rarg___lambda__2), 5, 4);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_errorWithLog___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_errorWithLog___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
static lean_object* _init_l_Lake_withLoggedIO___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_string_utf8_byte_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_11 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_5, x_8, x_9);
x_12 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_5, x_11, x_8);
x_13 = lean_string_utf8_extract(x_5, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_14 = l_Lake_withLoggedIO___rarg___lambda__2___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lake_instInhabitedLogEntry___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_apply_1(x_2, x_19);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_25, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = 1;
lean_inc(x_1);
x_8 = l_IO_FS_withIsolatedStreams___rarg(x_1, x_4, x_2, x_5, x_7);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___rarg___lambda__2), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_withLoggedIO___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = 3;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lake_getLogPos___rarg___closed__1;
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_13);
lean_inc(x_9);
x_16 = lean_alloc_closure((void*)(l_Lake_errorWithLog___rarg___lambda__2), 5, 4);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_8);
lean_closure_set(x_16, 3, x_9);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELog_error___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = 3;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lake_getLogPos___rarg___closed__1;
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_14);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lake_errorWithLog___rarg___lambda__2), 5, 4);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_9);
lean_closure_set(x_17, 3, x_10);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELog_monadError___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lake_getLogPos___rarg___closed__1;
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_8);
x_11 = lean_alloc_closure((void*)(l_Lake_ELog_failure___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELog_failure___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_dropLogFrom___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___rarg___lambda__2), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_3(x_7, lean_box(0), x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ELog_orElse___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lake_getLogPos___rarg___closed__1;
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_ELog_failure___rarg___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_4);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___rarg___lambda__2), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_3(x_8, lean_box(0), x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___rarg___lambda__1), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___rarg___lambda__2), 6, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogLogTOfMonad___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogLogTOfMonad___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___at_Lake_instMonadLogLogTOfMonad___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___at_Lake_instMonadLogLogTOfMonad___spec__1___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLogLogTOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_LogT_run___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LogT_run(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_LogT_run_x27___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LogT_run_x27___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_LogT_run_x27___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_LogT_run_x27___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LogT_run_x27___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = l_Lake_takeLog___rarg___closed__1;
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___rarg___lambda__2), 6, 5);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_1);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_LogT_takeAndRun___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___lambda__1___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
x_15 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_14, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_7, x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_20, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg(x_1, x_3, x_6, x_22, x_23, x_24);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_25, x_10);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_LogT_replayLog___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogELogTOfMonad___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___at_Lake_instMonadLogELogTOfMonad___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___at_Lake_instMonadLogELogTOfMonad___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___at_Lake_instMonadLogELogTOfMonad___spec__1___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLogELogTOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_array_get_size(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_apply_2(x_1, lean_box(0), x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_2(x_2, lean_box(0), x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_box(0);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
lean_inc(x_2);
x_10 = lean_apply_2(x_2, lean_box(0), x_4);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__2), 2, 1);
lean_closure_set(x_11, 0, x_2);
lean_inc(x_3);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__3), 3, 2);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_2);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_array_push(x_16, x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_inc(x_2);
x_20 = lean_apply_2(x_2, lean_box(0), x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__2), 2, 1);
lean_closure_set(x_21, 0, x_2);
lean_inc(x_3);
x_22 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__3), 3, 2);
lean_closure_set(x_23, 0, x_15);
lean_closure_set(x_23, 1, x_2);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_apply_2(x_2, lean_box(0), x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_apply_2(x_2, lean_box(0), x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = 3;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_6);
lean_inc(x_3);
x_13 = lean_apply_2(x_3, lean_box(0), x_12);
x_14 = l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1;
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_14, x_13);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__4), 4, 3);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_10);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5), 6, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_2, 1);
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_apply_2(x_1, lean_box(0), x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_5);
lean_inc(x_3);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1;
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg___lambda__1), 2, 1);
lean_closure_set(x_13, 0, x_3);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_1, x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_2(x_2, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = l_Array_shrink___rarg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_10);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_4);
x_12 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg___lambda__3), 3, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = l_Array_shrink___rarg(x_15, x_14);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_inc(x_1);
x_19 = lean_apply_2(x_1, lean_box(0), x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg___lambda__3), 3, 2);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_1);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_4, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg___lambda__4), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_2 = l_Lake_EStateT_instMonad___rarg(x_1);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg___lambda__2), 5, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg___lambda__5), 6, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_run___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_ELogT_run_x27___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_toExcept___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_run_x27___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_run_x27___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_ELogT_toLogT___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_toProd___rarg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_toLogT___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_toLogT___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_ELogT_toLogT_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_toProd_x3f___rarg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_toLogT_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_toLogT_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_toLogT_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_run_x3f___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lake_ELogT_run_x3f_x27___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_result_x3f___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_run_x3f_x27___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_run_x3f_x27___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_17);
lean_inc(x_16);
x_21 = l_Array_extract___rarg(x_17, x_16, x_20);
lean_dec(x_20);
x_22 = l_Array_shrink___rarg(x_17, x_16);
lean_dec(x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_22);
lean_ctor_set(x_4, 0, x_21);
x_23 = lean_apply_2(x_19, lean_box(0), x_4);
x_24 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___rarg___lambda__1), 2, 1);
lean_closure_set(x_24, 0, x_2);
x_25 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_array_get_size(x_27);
lean_inc(x_26);
x_31 = l_Array_extract___rarg(x_27, x_26, x_30);
lean_dec(x_30);
x_32 = l_Array_shrink___rarg(x_27, x_26);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_apply_2(x_29, lean_box(0), x_33);
x_35 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___rarg___lambda__1), 2, 1);
lean_closure_set(x_35, 0, x_2);
x_36 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_1(x_3, x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___rarg___lambda__2), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_toLogT_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_captureLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ELogT_captureLog___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_8, x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_14, x_13);
x_16 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_6);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = l_Lake_takeLog___rarg___closed__1;
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___rarg___lambda__2), 7, 6);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_1);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_3);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___lambda__1___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___lambda__1___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_array_get_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_4);
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_8, x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_11);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_21 = 0;
x_22 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg(x_1, x_2, x_5, x_21, x_22, x_23);
x_25 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_24, x_11);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = lean_array_get_size(x_26);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
lean_inc(x_27);
x_32 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_32, 0, x_27);
if (x_31 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_box(0);
x_35 = lean_apply_2(x_33, lean_box(0), x_34);
x_36 = lean_apply_4(x_28, lean_box(0), lean_box(0), x_35, x_32);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_29, x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_38, lean_box(0), x_39);
x_41 = lean_apply_4(x_28, lean_box(0), lean_box(0), x_40, x_32);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
x_42 = 0;
x_43 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_44 = lean_box(0);
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg(x_1, x_2, x_26, x_42, x_43, x_44);
x_46 = lean_apply_4(x_28, lean_box(0), lean_box(0), x_45, x_32);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___rarg___lambda__3), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_ELogT_replayLog_x3f___spec__2___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_ELogT_replayLog_x3f___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ELogT_replayLog_x3f___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_35 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___rarg___lambda__1___boxed), 2, 1);
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
x_7 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___rarg___lambda__2), 4, 3);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogIO_toBaseIO_replay___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_LogIO_toBaseIO_replay___spec__1(x_2, x_1, x_12, x_13, x_14, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LogIO_toBaseIO_replay___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_LogIO_toBaseIO_replay___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO_replay___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LogIO_toBaseIO_replay(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_OutStream_get(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___rarg___lambda__1___boxed), 5, 3);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_15 = lean_apply_2(x_1, x_14, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_Lake_LogIO_toBaseIO_replay(x_19, x_13, x_17);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_box(0);
x_33 = l_Lake_LogIO_toBaseIO_replay(x_31, x_13, x_30);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
return x_9;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_9, 0);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_9);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
return x_6;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_LogIO_toBaseIO___rarg___lambda__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_LogIO_toBaseIO___rarg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Lake_ELogT_toLogT_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_LogIO_captureLog___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = 3;
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
x_6 = lean_apply_2(x_2, x_5, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadErrorLoggerIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_io_error_to_string(x_9);
x_12 = 3;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_apply_2(x_2, x_13, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftIOLoggerIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = lean_apply_2(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_5 = lean_apply_2(x_1, x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_5);
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_11, x_16, x_17, x_18, x_2, x_8);
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_35 = lean_box(0);
x_36 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_26, x_33, x_34, x_35, x_2, x_24);
lean_dec(x_26);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_5, 1);
x_42 = lean_ctor_get(x_5, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
x_47 = lean_box(0);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_47);
return x_5;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_44, x_44);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
x_49 = lean_box(0);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_49);
return x_5;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_5);
x_50 = 0;
x_51 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_43, x_50, x_51, x_52, x_2, x_41);
lean_dec(x_43);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_dec(x_5);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_dec(x_6);
x_60 = lean_array_get_size(x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_60, x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = lean_box(0);
x_71 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_59, x_68, x_69, x_70, x_2, x_58);
lean_dec(x_59);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftLogIOLoggerIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_instMonadLiftLogIOLoggerIO___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_OutStream_get(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___rarg___lambda__1___boxed), 5, 3);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = lean_apply_2(x_1, x_13, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
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
lean_dec(x_7);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
return x_6;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LoggerIO_toBaseIO___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_LoggerIO_toBaseIO___rarg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_st_ref_take(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_push(x_5, x_2);
x_8 = lean_st_ref_set(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1;
x_4 = lean_st_mk_ref(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_apply_2(x_1, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_st_ref_get(x_5, x_11);
lean_dec(x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_15);
lean_ctor_set(x_12, 0, x_8);
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
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_8);
lean_dec(x_10);
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
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_st_ref_get(x_5, x_25);
lean_dec(x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_35 = x_26;
} else {
 lean_dec_ref(x_26);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 1);
x_39 = lean_ctor_get(x_8, 0);
lean_dec(x_39);
x_40 = lean_st_ref_get(x_5, x_38);
lean_dec(x_5);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_box(0);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_42);
lean_ctor_set(x_8, 0, x_43);
lean_ctor_set(x_40, 0, x_8);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_box(0);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_44);
lean_ctor_set(x_8, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_free_object(x_8);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_st_ref_get(x_5, x_52);
lean_dec(x_5);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
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
}
}
else
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
return x_4;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_4);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LoggerIO_captureLog___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_LoggerIO_captureLog___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LoggerIO_run_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
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
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_LoggerIO_run_x3f_x27___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EStateT(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EStateT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
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
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__1);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__2);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__3);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__4);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__5);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__6);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__7);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__8);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__9 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__9();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__9);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__10);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__11 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__11();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__11);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__12 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__12();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__12);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__13 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__13();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__13);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__14 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__14();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__14);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__15 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__15();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__15);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__16);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__17 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__17();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__17);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__18 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__18();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__18);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__19 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__19();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__19);
l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__20 = _init_l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__20();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprVerbosity____x40_Lake_Util_Log___hyg_10____closed__20);
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
l_Lake_Ansi_chalk___closed__1 = _init_l_Lake_Ansi_chalk___closed__1();
lean_mark_persistent(l_Lake_Ansi_chalk___closed__1);
l_Lake_Ansi_chalk___closed__2 = _init_l_Lake_Ansi_chalk___closed__2();
lean_mark_persistent(l_Lake_Ansi_chalk___closed__2);
l_Lake_Ansi_chalk___closed__3 = _init_l_Lake_Ansi_chalk___closed__3();
lean_mark_persistent(l_Lake_Ansi_chalk___closed__3);
l_Lake_instInhabitedLogLevel = _init_l_Lake_instInhabitedLogLevel();
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__1);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__2);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__3);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__4);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__5);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__6);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__7);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__8);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__9 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__9();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__9);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__10 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__10();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__10);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__11 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__11();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__11);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__12 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__12();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__12);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__13 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__13();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__13);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__14);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__15 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__15();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__15);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__16 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__16();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__16);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__17 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__17();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__17);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__18 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__18();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__18);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__19 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__19();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__19);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__20);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__21 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__21();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__21);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__22 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__22();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__22);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__23 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__23();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__23);
l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__24 = _init_l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__24();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_reprLogLevel____x40_Lake_Util_Log___hyg_509____closed__24);
l_Lake_instReprLogLevel___closed__1 = _init_l_Lake_instReprLogLevel___closed__1();
lean_mark_persistent(l_Lake_instReprLogLevel___closed__1);
l_Lake_instReprLogLevel = _init_l_Lake_instReprLogLevel();
lean_mark_persistent(l_Lake_instReprLogLevel);
l_Lake_instOrdLogLevel___closed__1 = _init_l_Lake_instOrdLogLevel___closed__1();
lean_mark_persistent(l_Lake_instOrdLogLevel___closed__1);
l_Lake_instOrdLogLevel = _init_l_Lake_instOrdLogLevel();
lean_mark_persistent(l_Lake_instOrdLogLevel);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__1);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__2);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__3);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__4);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__5);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__6);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__7);
l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogLevel____x40_Lake_Util_Log___hyg_876____closed__8);
l_Lake_instToJsonLogLevel___closed__1 = _init_l_Lake_instToJsonLogLevel___closed__1();
lean_mark_persistent(l_Lake_instToJsonLogLevel___closed__1);
l_Lake_instToJsonLogLevel = _init_l_Lake_instToJsonLogLevel();
lean_mark_persistent(l_Lake_instToJsonLogLevel);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__1___closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__3 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__2___closed__3);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__3___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____lambda__4___closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogLevel____x40_Lake_Util_Log___hyg_921____closed__3);
l_Lake_instFromJsonLogLevel___closed__1 = _init_l_Lake_instFromJsonLogLevel___closed__1();
lean_mark_persistent(l_Lake_instFromJsonLogLevel___closed__1);
l_Lake_instFromJsonLogLevel = _init_l_Lake_instFromJsonLogLevel();
lean_mark_persistent(l_Lake_instFromJsonLogLevel);
l_Lake_instLTLogLevel = _init_l_Lake_instLTLogLevel();
lean_mark_persistent(l_Lake_instLTLogLevel);
l_Lake_instLELogLevel = _init_l_Lake_instLELogLevel();
lean_mark_persistent(l_Lake_instLELogLevel);
l_Lake_LogLevel_ansiColor___closed__1 = _init_l_Lake_LogLevel_ansiColor___closed__1();
lean_mark_persistent(l_Lake_LogLevel_ansiColor___closed__1);
l_Lake_LogLevel_ansiColor___closed__2 = _init_l_Lake_LogLevel_ansiColor___closed__2();
lean_mark_persistent(l_Lake_LogLevel_ansiColor___closed__2);
l_Lake_LogLevel_ansiColor___closed__3 = _init_l_Lake_LogLevel_ansiColor___closed__3();
lean_mark_persistent(l_Lake_LogLevel_ansiColor___closed__3);
l_Lake_LogLevel_ofString_x3f___closed__1 = _init_l_Lake_LogLevel_ofString_x3f___closed__1();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__1);
l_Lake_LogLevel_ofString_x3f___closed__2 = _init_l_Lake_LogLevel_ofString_x3f___closed__2();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__2);
l_Lake_LogLevel_ofString_x3f___closed__3 = _init_l_Lake_LogLevel_ofString_x3f___closed__3();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__3);
l_Lake_LogLevel_ofString_x3f___closed__4 = _init_l_Lake_LogLevel_ofString_x3f___closed__4();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__4);
l_Lake_LogLevel_ofString_x3f___closed__5 = _init_l_Lake_LogLevel_ofString_x3f___closed__5();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__5);
l_Lake_LogLevel_ofString_x3f___closed__6 = _init_l_Lake_LogLevel_ofString_x3f___closed__6();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__6);
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
l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__1);
l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1402____closed__2);
l_Lake_instToJsonLogEntry___closed__1 = _init_l_Lake_instToJsonLogEntry___closed__1();
lean_mark_persistent(l_Lake_instToJsonLogEntry___closed__1);
l_Lake_instToJsonLogEntry = _init_l_Lake_instToJsonLogEntry();
lean_mark_persistent(l_Lake_instToJsonLogEntry);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__1 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__1();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__1);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__2 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__2();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__2);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__3 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__3();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__3);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__4);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__5 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__5();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__5);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__6 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__6();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__6);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__7);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__8 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__8();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__8);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__9 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__9();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__9);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__10 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__10();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__10);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__11);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__12);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__13 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__13();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__13);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__14 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__14();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__14);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__15 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__15();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__15);
l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16 = _init_l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1454____closed__16);
l_Lake_instFromJsonLogEntry___closed__1 = _init_l_Lake_instFromJsonLogEntry___closed__1();
lean_mark_persistent(l_Lake_instFromJsonLogEntry___closed__1);
l_Lake_instFromJsonLogEntry = _init_l_Lake_instFromJsonLogEntry();
lean_mark_persistent(l_Lake_instFromJsonLogEntry);
l_Lake_LogEntry_toString___closed__1 = _init_l_Lake_LogEntry_toString___closed__1();
lean_mark_persistent(l_Lake_LogEntry_toString___closed__1);
l_Lake_LogEntry_toString___closed__2 = _init_l_Lake_LogEntry_toString___closed__2();
lean_mark_persistent(l_Lake_LogEntry_toString___closed__2);
l_Lake_logSerialMessage___rarg___closed__1 = _init_l_Lake_logSerialMessage___rarg___closed__1();
lean_mark_persistent(l_Lake_logSerialMessage___rarg___closed__1);
l_Lake_logSerialMessage___rarg___closed__2 = _init_l_Lake_logSerialMessage___rarg___closed__2();
lean_mark_persistent(l_Lake_logSerialMessage___rarg___closed__2);
l_Lake_instInhabitedLog___closed__1 = _init_l_Lake_instInhabitedLog___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLog___closed__1);
l_Lake_instInhabitedLog = _init_l_Lake_instInhabitedLog();
lean_mark_persistent(l_Lake_instInhabitedLog);
l_Lake_instFromJsonLog___closed__1 = _init_l_Lake_instFromJsonLog___closed__1();
lean_mark_persistent(l_Lake_instFromJsonLog___closed__1);
l_Lake_instFromJsonLog___closed__2 = _init_l_Lake_instFromJsonLog___closed__2();
lean_mark_persistent(l_Lake_instFromJsonLog___closed__2);
l_Lake_Log_instInhabitedPos = _init_l_Lake_Log_instInhabitedPos();
lean_mark_persistent(l_Lake_Log_instInhabitedPos);
l_Lake_instOfNatPos = _init_l_Lake_instOfNatPos();
lean_mark_persistent(l_Lake_instOfNatPos);
l_Lake_instLTPos = _init_l_Lake_instLTPos();
lean_mark_persistent(l_Lake_instLTPos);
l_Lake_instLEPos = _init_l_Lake_instLEPos();
lean_mark_persistent(l_Lake_instLEPos);
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
l_Lake_getLogPos___rarg___closed__1 = _init_l_Lake_getLogPos___rarg___closed__1();
lean_mark_persistent(l_Lake_getLogPos___rarg___closed__1);
l_Lake_takeLog___rarg___closed__1 = _init_l_Lake_takeLog___rarg___closed__1();
lean_mark_persistent(l_Lake_takeLog___rarg___closed__1);
l_Lake_withLoggedIO___rarg___lambda__2___closed__1 = _init_l_Lake_withLoggedIO___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lake_withLoggedIO___rarg___lambda__2___closed__1);
l_Lake_LogT_run_x27___rarg___closed__1 = _init_l_Lake_LogT_run_x27___rarg___closed__1();
lean_mark_persistent(l_Lake_LogT_run_x27___rarg___closed__1);
l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1 = _init_l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1();
lean_mark_persistent(l_Lake_instMonadErrorELogTOfMonad___rarg___lambda__5___closed__1);
l_Lake_ELogT_run_x27___rarg___closed__1 = _init_l_Lake_ELogT_run_x27___rarg___closed__1();
lean_mark_persistent(l_Lake_ELogT_run_x27___rarg___closed__1);
l_Lake_ELogT_toLogT___rarg___closed__1 = _init_l_Lake_ELogT_toLogT___rarg___closed__1();
lean_mark_persistent(l_Lake_ELogT_toLogT___rarg___closed__1);
l_Lake_ELogT_toLogT_x3f___rarg___closed__1 = _init_l_Lake_ELogT_toLogT_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_ELogT_toLogT_x3f___rarg___closed__1);
l_Lake_ELogT_run_x3f_x27___rarg___closed__1 = _init_l_Lake_ELogT_run_x3f_x27___rarg___closed__1();
lean_mark_persistent(l_Lake_ELogT_run_x3f_x27___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
