// Lean compiler output
// Module: Lake.Util.Log
// Imports: Init.System.IO Init.Data.Repr Init.Data.Ord.Basic Lean.Data.Json Lake.Util.Error Lake.Util.EStateT Lean.Message Lake.Util.Lift
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
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqLogLevel(uint8_t, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__13____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofMessageSeverity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_isEmpty___boxed(lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__4____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Log_instAppend___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerbosity;
LEAN_EXPORT lean_object* l_Lake_instOrdLogLevel;
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdPos;
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel;
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_reprLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_9____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
LEAN_EXPORT lean_object* l_Lake_Log_instAppend;
static lean_object* l_Lake_reprLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___boxed(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__0;
LEAN_EXPORT lean_object* l_Lake_Log_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object*);
static lean_object* l_Lake_instToJsonLogEntry___closed__0;
LEAN_EXPORT uint8_t l_Lake_instInhabitedVerbosity;
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinPos;
LEAN_EXPORT lean_object* l_Lake_Log_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLogLevel;
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogLevel___lam__0___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
static lean_object* l_Lake_reprAnsiMode___closed__0____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_instToJsonLogLevel;
LEAN_EXPORT lean_object* l_Lake_instLTLogLevel;
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instInhabitedPos;
static lean_object* l_Lake_Log_empty___closed__0;
LEAN_EXPORT uint8_t l_Lake_Log_decEqPos____x40_Lake_Util_Log_1404496646____hygCtx___hyg_18_(lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
static lean_object* l_Lake_AnsiMode_noConfusion___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
static lean_object* l_Lake_reprVerbosity___closed__3____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_fromJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lake_Log_instToString___closed__0;
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object*);
static lean_object* l_Lake_Log_filter___closed__9;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprAnsiMode;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
static lean_object* l_Lake_ELogT_toLogT___redArg___closed__0;
static lean_object* l_Lake_LogEntry_ofSerialMessage___closed__0;
LEAN_EXPORT uint8_t l_Lake_Log_instDecidableEqPos(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonLogEntry___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object*);
lean_object* l_Lake_EResult_toProd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ansiColor___closed__0;
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__3____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ofNat___boxed(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprVerbosity___closed__2____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLTVerbosity;
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
LEAN_EXPORT lean_object* l_Lake_LogEntry_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__2;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object*, lean_object*);
lean_object* l_Lake_EResult_result_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_extractLog___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonLogEntry;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_reprVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_6____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_minLogLv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__11____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__6____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqVerbosity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t, uint8_t);
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLog;
LEAN_EXPORT lean_object* l_Lake_reprLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_(uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__1;
static lean_object* l_Lake_instFromJsonLogLevel___closed__0;
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLTPos;
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_toJsonLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object*, lean_object*);
static lean_object* l_Lake_reprLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0;
uint32_t l_Char_toLower(uint32_t);
static lean_object* l_Lake_reprVerbosity___closed__5____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity;
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO;
LEAN_EXPORT uint8_t l_Lake_Log_hasEntries(lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdVerbosity;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedLog___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_maxLv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__7____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream;
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog;
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString(lean_object*, uint8_t);
static lean_object* l_Lake_fromJsonLogEntry___closed__8____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_info(lean_object*);
static lean_object* l_Lake_reprLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogLevel___lam__2___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Verbosity_minLogLv(uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadLiftLogIOLoggerIO___closed__1;
LEAN_EXPORT lean_object* l_Lake_instLEPos;
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedLogLevel;
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxPos;
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_reprVerbosity___closed__4____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27____boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_LogLevel_ofString_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_decEqPos____x40_Lake_Util_Log_1404496646____hygCtx___hyg_18____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(uint8_t, uint8_t);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Log_0__Lake_instToStringLogLevel;
LEAN_EXPORT uint8_t l_Lake_instDecidableRelPosLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx(lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
lean_object* l_Lake_EResult_toProd_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__7;
LEAN_EXPORT lean_object* l_Lake_reprAnsiMode____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__8;
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toString(uint8_t);
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object*, uint8_t, uint8_t);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_empty;
LEAN_EXPORT lean_object* l_Lake_reprAnsiMode____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__4;
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t);
static lean_object* l_Lake_reprLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_maxLv_spec__0(lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogEntry_toString___closed__1;
lean_object* l_Lake_EResult_toExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprAnsiMode___closed__0;
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqLogLevel___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_reprVerbosity___closed__0____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object*);
static lean_object* l_Lake_instInhabitedLogEntry___closed__1;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_withLoggedIO___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprLogLevel___closed__0;
LEAN_EXPORT lean_object* l_Lake_Log_instDecidableEqPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry;
LEAN_EXPORT lean_object* l_Lake_instToJsonLog;
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableRelPosLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lake_instMonadLiftLogIOLoggerIO___closed__0;
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Ansi_chalk___closed__0;
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogT_takeAndRun___redArg___closed__0;
static lean_object* l_Lake_instReprVerbosity___closed__0;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_instToString;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ansiColor___closed__1;
LEAN_EXPORT lean_object* l_Lake_Log_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__0;
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_ELogT_run_x27___redArg___closed__0;
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t);
static lean_object* l_Lake_Ansi_chalk___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__12____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
static lean_object* l_Lake_Log_filter___closed__6;
static lean_object* l_Lake_LogEntry_toString___closed__0;
static lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel;
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLogEntry;
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLEVerbosity;
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object*);
static lean_object* l_Lake_Ansi_chalk___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_size(lean_object*);
static lean_object* l_Lake_LogLevel_ansiColor___closed__2;
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO;
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_(lean_object*);
static lean_object* l_Lake_fromJsonLogLevel___lam__3___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogLevel;
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity;
static lean_object* l_Lake_fromJsonLogLevel___lam__1___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_reprVerbosity___closed__1____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_withLoggedIO___redArg___lam__2___closed__1;
static lean_object* l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprAnsiMode___closed__5____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOfNatPos;
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___boxed(lean_object*);
static lean_object* l_Lake_fromJsonLogLevel___lam__0___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream;
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_reprVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO;
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36____boxed(lean_object*);
static lean_object* l_Lake_reprAnsiMode___closed__1____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object*);
static lean_object* l_Lake_instOrdVerbosity___closed__0;
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprAnsiMode___closed__4____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Log_filter___closed__3;
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instOrdLogLevel___closed__0;
LEAN_EXPORT lean_object* l_Lake_instFromJsonLogEntry;
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadStateOfStateTOfMonad___redArg(lean_object*);
static lean_object* l_Lake_reprAnsiMode___closed__3____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instToJsonLogLevel___closed__0;
static lean_object* l_Lake_toJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instLELogLevel;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Log_filter___closed__5;
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx(uint8_t);
static lean_object* l_Lake_toJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_(lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object*);
static lean_object* l_Lake_reprAnsiMode___closed__2____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogEntry_warning(lean_object*);
LEAN_EXPORT lean_object* l_Lake_AnsiMode_isEnabled___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LogLevel_ofString_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedLogEntry___closed__0;
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_fromJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lake_Verbosity_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_Verbosity_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_Verbosity_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Verbosity_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Verbosity_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_Verbosity_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Verbosity_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lake_Verbosity_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__0____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Verbosity.quiet", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__1____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprVerbosity___closed__0____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__2____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Verbosity.normal", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__3____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprVerbosity___closed__2____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__4____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Verbosity.verbose", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__5____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprVerbosity___closed__4____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_reprVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (x_1) {
case 0:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_3 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_3 = x_27;
goto block_9;
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_10 = x_30;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_10 = x_31;
goto block_16;
}
}
default: 
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_17 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_17 = x_35;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_reprVerbosity___closed__1____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
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
x_11 = l_Lake_reprVerbosity___closed__3____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
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
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lake_reprVerbosity___closed__5____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_reprVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_6____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_reprVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprVerbosity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_reprVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_6____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprVerbosity___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Verbosity_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_1, x_4);
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
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
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
x_3 = l_Lake_Verbosity_ctorIdx(x_1);
x_4 = l_Lake_Verbosity_ctorIdx(x_2);
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
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instDecidableEqVerbosity(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
if (x_2 == 0)
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
switch (x_2) {
case 0:
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
case 1:
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
default: 
{
if (x_2 == 2)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdVerbosity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instOrdVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instOrdVerbosity___closed__0;
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
LEAN_EXPORT uint8_t l_Lake_instMinVerbosity___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18_(x_1, x_2);
if (x_3 == 2)
{
return x_2;
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Lake_instMinVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMinVerbosity___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinVerbosity___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instMinVerbosity___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxVerbosity___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_ordVerbosity____x40_Lake_Util_Log_99018267____hygCtx___hyg_18_(x_1, x_2);
if (x_3 == 2)
{
return x_1;
}
else
{
return x_2;
}
}
}
static lean_object* _init_l_Lake_instMaxVerbosity() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMaxVerbosity___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxVerbosity___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instMaxVerbosity___lam__0(x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lake_AnsiMode_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_AnsiMode_ctorIdx(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_AnsiMode_noConfusion___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Verbosity_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_AnsiMode_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_AnsiMode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_AnsiMode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_AnsiMode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lake_AnsiMode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_reprAnsiMode___closed__0____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.AnsiMode.auto", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_reprAnsiMode___closed__1____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprAnsiMode___closed__0____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprAnsiMode___closed__2____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.AnsiMode.ansi", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_reprAnsiMode___closed__3____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprAnsiMode___closed__2____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprAnsiMode___closed__4____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.AnsiMode.noAnsi", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_reprAnsiMode___closed__5____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprAnsiMode___closed__4____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_reprAnsiMode____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (x_1) {
case 0:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_3 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_3 = x_27;
goto block_9;
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_10 = x_30;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_10 = x_31;
goto block_16;
}
}
default: 
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_17 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_17 = x_35;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_reprAnsiMode___closed__1____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
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
x_11 = l_Lake_reprAnsiMode___closed__3____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
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
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lake_reprAnsiMode___closed__5____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_reprAnsiMode____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_reprAnsiMode____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprAnsiMode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_reprAnsiMode____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprAnsiMode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprAnsiMode___closed__0;
return x_1;
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
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
case 1:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
x_5 = l_Lake_AnsiMode_isEnabled(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Ansi_chalk___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\x1b[1;", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Ansi_chalk___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("m", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Ansi_chalk___closed__2() {
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
x_3 = l_Lake_Ansi_chalk___closed__0;
x_4 = lean_string_append(x_3, x_1);
x_5 = l_Lake_Ansi_chalk___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_string_append(x_6, x_2);
x_8 = l_Lake_Ansi_chalk___closed__2;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Ansi_chalk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Ansi_chalk(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lake_OutStream_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutStream_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
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
lean_inc_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lake_instCoeStreamOutStream___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeStreamOutStream() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeStreamOutStream___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHandleOutStream___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_stream_of_handle(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instCoeHandleOutStream() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeHandleOutStream___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lake_LogLevel_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_LogLevel_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_AnsiMode_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_LogLevel_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_LogLevel_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lake_LogLevel_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
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
static lean_object* _init_l_Lake_reprLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.trace", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.info", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.warning", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.LogLevel.error", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_reprLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_reprLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; 
switch (x_1) {
case 0:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_3 = x_33;
goto block_9;
}
else
{
lean_object* x_34; 
x_34 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_3 = x_34;
goto block_9;
}
}
case 1:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_10 = x_37;
goto block_16;
}
else
{
lean_object* x_38; 
x_38 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_10 = x_38;
goto block_16;
}
}
case 2:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_17 = x_41;
goto block_23;
}
else
{
lean_object* x_42; 
x_42 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_17 = x_42;
goto block_23;
}
}
default: 
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_24 = x_45;
goto block_30;
}
else
{
lean_object* x_46; 
x_46 = l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_;
x_24 = x_46;
goto block_30;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_reprLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
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
x_11 = l_Lake_reprLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
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
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lake_reprLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lake_reprLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_reprLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_9____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_reprLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprLogLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_reprLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_9____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprLogLevel___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 3;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_le(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
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
x_3 = l_Lake_LogLevel_ctorIdx(x_1);
x_4 = l_Lake_LogLevel_ctorIdx(x_2);
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
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instDecidableEqLogLevel(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
if (x_2 == 0)
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
switch (x_2) {
case 0:
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
case 1:
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
case 2:
{
switch (x_2) {
case 2:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
case 3:
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
default: 
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
}
default: 
{
if (x_2 == 3)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 2;
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instOrdLogLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instOrdLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instOrdLogLevel___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lake_toJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lake_toJsonLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lake_toJsonLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_Lake_toJsonLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonLogLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonLogLevel___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___lam__0___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___lam__0___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonLogLevel___lam__0___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_fromJsonLogLevel___lam__0___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___lam__1___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
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
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec_ref(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec_ref(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_7);
x_13 = l_Lake_fromJsonLogLevel___lam__1___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
x_14 = l_Except_orElseLazy___redArg(x_13, x_4);
return x_14;
}
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___lam__2___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
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
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec_ref(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec_ref(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_7);
x_13 = l_Lake_fromJsonLogLevel___lam__2___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
x_14 = l_Except_orElseLazy___redArg(x_13, x_4);
return x_14;
}
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___lam__3___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
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
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec_ref(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec_ref(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_7);
x_13 = l_Lake_fromJsonLogLevel___lam__3___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
x_14 = l_Except_orElseLazy___redArg(x_13, x_4);
return x_14;
}
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_fromJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_() {
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
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_alloc_closure((void*)(l_Lake_fromJsonLogLevel___lam__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_), 1, 0);
x_3 = l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lake_fromJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_fromJsonLogLevel___lam__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
lean_closure_set(x_6, 3, x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_fromJsonLogLevel___lam__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_fromJsonLogLevel___lam__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_7);
x_9 = l_Lean_Json_parseTagged(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Except_orElseLazy___redArg(x_9, x_8);
lean_dec_ref(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Except_orElseLazy___redArg(x_13, x_8);
lean_dec_ref(x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_9);
x_15 = l_Lake_fromJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_;
x_16 = l_Except_orElseLazy___redArg(x_15, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_fromJsonLogLevel___lam__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_fromJsonLogLevel___lam__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonLogLevel___lam__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_46____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_fromJsonLogLevel___lam__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instFromJsonLogLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_fromJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonLogLevel___closed__0;
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
LEAN_EXPORT uint8_t l_Lake_instMinLogLevel___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(x_1, x_2);
if (x_3 == 2)
{
return x_2;
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Lake_instMinLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMinLogLevel___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinLogLevel___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instMinLogLevel___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instMaxLogLevel___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(x_1, x_2);
if (x_3 == 2)
{
return x_1;
}
else
{
return x_2;
}
}
}
static lean_object* _init_l_Lake_instMaxLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMaxLogLevel___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxLogLevel___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instMaxLogLevel___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint32_t l_Lake_LogLevel_icon(uint8_t x_1) {
_start:
{
switch (x_1) {
case 2:
{
uint32_t x_2; 
x_2 = 9888;
return x_2;
}
case 3:
{
uint32_t x_3; 
x_3 = 10006;
return x_3;
}
default: 
{
uint32_t x_4; 
x_4 = 8505;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_icon___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_LogLevel_icon(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_LogLevel_ansiColor___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("33", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ansiColor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("31", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ansiColor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("34", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor(uint8_t x_1) {
_start:
{
switch (x_1) {
case 2:
{
lean_object* x_2; 
x_2 = l_Lake_LogLevel_ansiColor___closed__0;
return x_2;
}
case 3:
{
lean_object* x_3; 
x_3 = l_Lake_LogLevel_ansiColor___closed__1;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lake_LogLevel_ansiColor___closed__2;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogLevel_ansiColor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_LogLevel_ansiColor(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_LogLevel_ofString_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_Char_toLower(x_4);
x_6 = lean_string_utf8_set(x_2, x_1, x_5);
x_7 = lean_string_utf8_next(x_6, x_1);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__0() {
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
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__1() {
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
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("information", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warn", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__4() {
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
static lean_object* _init_l_Lake_LogLevel_ofString_x3f___closed__5() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_mapAux___at___Lake_LogLevel_ofString_x3f_spec__0(x_6, x_1);
x_8 = l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_LogLevel_ofString_x3f___closed__2;
x_13 = lean_string_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lake_LogLevel_ofString_x3f___closed__3;
x_15 = lean_string_dec_eq(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_17 = lean_string_dec_eq(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
x_19 = lean_string_dec_eq(x_7, x_18);
lean_dec_ref(x_7);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lake_LogLevel_ofString_x3f___closed__4;
return x_21;
}
}
else
{
lean_dec_ref(x_7);
goto block_5;
}
}
else
{
lean_dec_ref(x_7);
goto block_5;
}
}
else
{
lean_dec_ref(x_7);
goto block_3;
}
}
else
{
lean_dec_ref(x_7);
goto block_3;
}
}
else
{
lean_object* x_22; 
lean_dec_ref(x_7);
x_22 = l_Lake_LogLevel_ofString_x3f___closed__5;
return x_22;
}
block_3:
{
lean_object* x_2; 
x_2 = l_Lake_LogLevel_ofString_x3f___closed__0;
return x_2;
}
block_5:
{
lean_object* x_4; 
x_4 = l_Lake_LogLevel_ofString_x3f___closed__1;
return x_4;
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
x_2 = l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_;
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
x_3 = l_Lake_LogLevel_toString(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LogLevel_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Util_Log_0__Lake_instToStringLogLevel() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0;
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
x_3 = l_Lake_LogLevel_ofMessageSeverity(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_LogLevel_toMessageSeverity(uint8_t x_1) {
_start:
{
switch (x_1) {
case 2:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 3:
{
uint8_t x_3; 
x_3 = 2;
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
LEAN_EXPORT lean_object* l_Lake_LogLevel_toMessageSeverity___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
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
x_3 = l_Lake_Verbosity_minLogLv(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedLogEntry___closed__0;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLogEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("level", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
x_5 = l_Lake_toJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
lean_inc_ref(x_3);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lake_toJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27__spec__0(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToJsonLogEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonLogEntry___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lake_fromJsonLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LogEntry", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_2 = l_Lake_fromJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__3____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_fromJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__4____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonLogEntry___closed__4____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_2 = l_Lake_fromJsonLogEntry___closed__3____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__6____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__7____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_fromJsonLogEntry___closed__6____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__8____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonLogEntry___closed__7____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_2 = l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_2 = l_Lake_fromJsonLogEntry___closed__8____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__11____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__12____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_fromJsonLogEntry___closed__11____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__13____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonLogEntry___closed__12____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_2 = l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_2 = l_Lake_fromJsonLogEntry___closed__13____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
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
x_9 = l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_;
x_17 = l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__1(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unbox(x_15);
lean_dec(x_15);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_15);
lean_dec(x_15);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37__spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonLogEntry___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_LogEntry_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LogEntry_toString___closed__1() {
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
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lake_LogLevel_toString(x_3);
x_6 = l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_string_append(x_7, x_4);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lake_LogLevel_ansiColor(x_9);
x_12 = l_Lake_LogLevel_toString(x_9);
x_13 = l_Lake_LogEntry_toString___closed__0;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lake_Ansi_chalk(x_11, x_14);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_16 = l_Lake_LogEntry_toString___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_toString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_LogEntry_toString(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = l_Lake_LogEntry_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToStringLogEntry() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToStringLogEntry___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringLogEntry___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToStringLogEntry___lam__0(x_1);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lake_LogEntry_ofSerialMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_6 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_6);
x_16 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_6, x_15, x_14);
x_17 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_6, x_16, x_15);
x_18 = lean_string_utf8_extract(x_6, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_6);
x_19 = lean_string_utf8_byte_size(x_18);
x_20 = lean_nat_dec_eq(x_19, x_14);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = l_Lake_LogEntry_ofSerialMessage___closed__0;
x_22 = lean_string_append(x_18, x_21);
x_23 = lean_string_utf8_byte_size(x_7);
x_24 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_7, x_23, x_14);
x_25 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_7, x_24, x_23);
x_26 = lean_string_utf8_extract(x_7, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
x_27 = lean_string_append(x_22, x_26);
lean_dec_ref(x_26);
x_8 = x_27;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_18);
x_28 = lean_string_utf8_byte_size(x_7);
x_29 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_7, x_28, x_14);
x_30 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_7, x_29, x_28);
x_31 = lean_string_utf8_extract(x_7, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
x_8 = x_31;
goto block_13;
}
block_13:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lake_LogLevel_ofMessageSeverity(x_5);
x_10 = lean_box(0);
x_11 = l_Lean_mkErrorStringWithPos(x_3, x_4, x_8, x_10, x_10, x_10);
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogEntry_ofMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_MessageData_toString(x_7, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_string_utf8_byte_size(x_6);
x_21 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_6, x_20, x_19);
x_22 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_6, x_21, x_20);
x_23 = lean_string_utf8_extract(x_6, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_6);
x_24 = lean_string_utf8_byte_size(x_23);
x_25 = lean_nat_dec_eq(x_24, x_19);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lake_LogEntry_ofSerialMessage___closed__0;
x_27 = lean_string_append(x_23, x_26);
x_28 = lean_string_utf8_byte_size(x_9);
x_29 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_9, x_28, x_19);
x_30 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_9, x_29, x_28);
x_31 = lean_string_utf8_extract(x_9, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
x_32 = lean_string_append(x_27, x_31);
lean_dec_ref(x_31);
x_12 = x_32;
goto block_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_23);
x_33 = lean_string_utf8_byte_size(x_9);
x_34 = l_Substring_takeWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__0(x_9, x_33, x_19);
x_35 = l_Substring_takeRightWhileAux___at___Lake_LogEntry_ofSerialMessage_spec__1(x_9, x_34, x_33);
x_36 = lean_string_utf8_extract(x_9, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_9);
x_12 = x_36;
goto block_18;
}
block_18:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lake_LogLevel_ofMessageSeverity(x_5);
x_14 = lean_box(0);
x_15 = l_Lean_mkErrorStringWithPos(x_3, x_4, x_12, x_14, x_14, x_14);
lean_dec_ref(x_12);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_11)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_11;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_logVerbose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_logVerbose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_logVerbose(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_logInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 1;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_logInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_logInfo(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logWarning___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_logWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 2;
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_logError___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_logError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 3;
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = l_Lake_LogEntry_ofSerialMessage(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5 + 2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_3);
x_7 = l_Lake_LogEntry_ofSerialMessage(x_2);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_logMessage___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = lean_alloc_closure((void*)(l_Lake_LogEntry_ofMessage), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logToStream(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(x_3, x_6);
if (x_7 == 2)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lake_LogEntry_toString(x_1, x_4);
x_11 = l_IO_FS_Stream_putStrLn(x_2, x_10, x_5);
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
}
LEAN_EXPORT lean_object* l_Lake_logToStream___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
x_7 = lean_unbox(x_4);
x_8 = l_Lake_logToStream(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_nop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLog_nop___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instInhabitedOfPure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MonadLog_instInhabitedOfPure___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_lift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_MonadLog_lift___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_instOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_instOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_MonadLog_instOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_4);
x_7 = lean_box(x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_MonadLog_stream___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_MonadLog_stream___redArg___lam__0(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lake_MonadLog_stream___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stream___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
x_7 = lean_unbox(x_5);
x_8 = l_Lake_MonadLog_stream(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 4);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = 3;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_error(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 3;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_apply_1(x_4, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = l_Lake_OutStream_get(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unbox(x_10);
lean_dec(x_10);
x_13 = l_Lake_logToStream(x_2, x_7, x_3, x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
x_7 = lean_unbox(x_4);
x_8 = l_Lake_OutStream_logEntry(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(x_2);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_4);
x_7 = lean_box(x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_OutStream_logger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_OutStream_logger___redArg___lam__0(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lake_OutStream_logger___redArg(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_logger___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_4);
x_7 = lean_unbox(x_5);
x_8 = l_Lake_OutStream_logger(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(x_2);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_OutStream_logEntry___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_box(x_2);
x_6 = lean_box(x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_box(x_3);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_MonadLog_stdout___redArg___lam__0(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lean_unbox(x_3);
x_6 = l_Lake_MonadLog_stdout___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stdout___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lake_MonadLog_stdout(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(1);
x_5 = lean_box(x_2);
x_6 = lean_box(x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_box(x_3);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_MonadLog_stdout___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lean_unbox(x_3);
x_6 = l_Lake_MonadLog_stderr___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_stderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lake_MonadLog_stderr(x_1, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lake_OutStream_get(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
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
x_17 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
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
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lake_OutStream_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_8);
x_10 = l_Lake_AnsiMode_isEnabled(x_8, x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(x_4);
x_14 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_2);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_box(x_4);
x_18 = lean_alloc_closure((void*)(l_Lake_OutStream_getLogger___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_OutStream_getLogger___redArg___lam__0(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
x_7 = lean_unbox(x_4);
x_8 = l_Lake_OutStream_getLogger___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutStream_getLogger___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_4);
x_8 = lean_unbox(x_5);
x_9 = l_Lake_OutStream_getLogger(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_MonadLogT_instInhabitedOfPure___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_3, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_apply_2(x_7, lean_box(0), x_4);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_1(x_6, x_8);
x_10 = lean_apply_1(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_adaptMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_MonadLogT_adaptMethods(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLogT_ignoreLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_MonadLog_nop___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedLog___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLog___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonLog___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_toJson___redArg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonLog() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instToJsonLogEntry___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lake_instToJsonLog___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonLog___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
static lean_object* _init_l_Lake_instFromJsonLog() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instFromJsonLogEntry___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lake_instFromJsonLog___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
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
LEAN_EXPORT uint8_t l_Lake_Log_decEqPos____x40_Lake_Util_Log_1404496646____hygCtx___hyg_18_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_decEqPos____x40_Lake_Util_Log_1404496646____hygCtx___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Log_decEqPos____x40_Lake_Util_Log_1404496646____hygCtx___hyg_18_(x_1, x_2);
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
LEAN_EXPORT uint8_t l_Lake_instOrdPos___lam__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_instOrdPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instOrdPos___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdPos___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instOrdPos___lam__0(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_instMinPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMinPos___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMinPos___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMinPos___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_instMaxPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMaxPos___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMaxPos___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMaxPos___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Log_empty___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Log_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Log_empty___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Log_instEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Log_empty___closed__0;
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
x_5 = l_instDecidableNot___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_hasEntries___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Log_hasEntries(x_1);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
x_3 = l_Array_append___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_append(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Log_instAppend___closed__0() {
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
x_1 = l_Lake_Log_instAppend___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_extract___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_extract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Log_extract(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_dropFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___redArg(x_1, x_2);
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
x_4 = l_Array_extract___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_takeFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Log_takeFrom(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_split(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_1);
x_3 = l_Array_shrink___redArg(x_1, x_2);
x_4 = lean_array_get_size(x_1);
x_5 = l_Array_extract___redArg(x_1, x_2, x_4);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_LogEntry_toString(x_6, x_5);
lean_dec_ref(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___closed__0;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lake_instInhabitedLogEntry___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Log_toString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Log_instToString___closed__0() {
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
x_1 = l_Lake_Log_instToString___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_5, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_6);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = 0;
x_17 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_15, x_3, x_16, x_17, x_6);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_7);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_16, 0, x_3);
x_17 = 0;
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_16, x_4, x_17, x_18, x_7);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc_ref(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = lean_array_push(x_2, x_3);
return x_6;
}
}
}
static lean_object* _init_l_Lake_Log_filter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Log_filter___closed__1;
x_2 = l_Lake_Log_filter___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_Log_filter___closed__5;
x_2 = l_Lake_Log_filter___closed__4;
x_3 = l_Lake_Log_filter___closed__3;
x_4 = l_Lake_Log_filter___closed__2;
x_5 = l_Lake_Log_filter___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Log_filter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Log_filter___closed__6;
x_2 = l_Lake_Log_filter___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_filter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = l_Lake_Log_empty___closed__0;
x_6 = l_Lake_Log_filter___closed__9;
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lake_Log_filter___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_2, x_10, x_11, x_5);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Log_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = l_Lake_Log_filter___closed__9;
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_alloc_closure((void*)(l_Lake_Log_any___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), x_5, x_7, x_2, x_8, x_9);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Log_any___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Log_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_maxLv_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec_ref(x_11);
x_13 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_21_(x_4, x_12);
if (x_13 == 2)
{
if (x_10 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
x_5 = x_12;
goto block_9;
}
}
else
{
x_5 = x_12;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Log_maxLv(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_maxLv_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_maxLv_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_maxLv_spec__0(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Log_maxLv___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Log_maxLv(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_array_push(x_2, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_pushLogEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_pushLogEntry___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadLog_ofMonadState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLog___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLog___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getLog(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_getLogPos___redArg___lam__0___boxed), 1, 0);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_getLogPos___redArg___lam__0___boxed), 1, 0);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLogPos___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLogPos___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Log_empty___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_takeLog___redArg___lam__0), 1, 0);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_takeLog___redArg___lam__0), 1, 0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
lean_inc(x_1);
x_4 = l_Array_extract___redArg(x_2, x_1, x_3);
x_5 = l_Array_shrink___redArg(x_2, x_1);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeLogFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_takeLogFrom___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Array_shrink___redArg(x_2, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_dropLogFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_dropLogFrom___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_dropLogFrom___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_extract___redArg(x_3, x_1, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_extractLog___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLogPos___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lake_extractLog___redArg___closed__0;
lean_inc(x_9);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = l_Lake_extractLog___redArg___closed__0;
lean_inc(x_10);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_extractLog___redArg___lam__2), 5, 4);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_10);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_extractLog___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_extractLog___redArg___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_4);
x_6 = l_Array_extract___redArg(x_4, x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__0), 5, 4);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lake_extractLog___redArg___closed__0;
lean_inc(x_9);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = l_Lake_extractLog___redArg___closed__0;
lean_inc(x_11);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lake_withExtractLog___redArg___lam__2), 5, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_5);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_11);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_withExtractLog___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_withExtractLog___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_3(x_5, lean_box(0), x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lake_extractLog___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = l_Lake_extractLog___redArg___closed__0;
x_13 = lean_alloc_closure((void*)(l_Lake_withLogErrorPos___redArg___lam__0), 3, 2);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_11);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_withLogErrorPos___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_withLogErrorPos___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_3(x_7, lean_box(0), x_2, x_3);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = l_Lake_extractLog___redArg___closed__0;
x_12 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_8);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_7);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_10);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = l_Lake_extractLog___redArg___closed__0;
x_14 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_10);
lean_inc(x_9);
x_15 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__2), 5, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_9);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_12);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_errorWithLog___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_errorWithLog___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_withLoggedIO___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_6);
x_11 = l_Lake_withLoggedIO___redArg___lam__2___closed__0;
x_12 = l_Lake_withLoggedIO___redArg___lam__2___closed__1;
x_13 = l_Substring_takeWhileAux(x_5, x_7, x_12, x_8);
x_14 = l_Substring_takeRightWhileAux(x_5, x_13, x_12, x_7);
x_15 = lean_string_utf8_extract(x_5, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_16 = lean_string_append(x_11, x_15);
lean_dec_ref(x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_apply_1(x_2, x_18);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__0), 3, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_6);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_1, lean_box(0), x_22);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_IO_FS_withIsolatedStreams___redArg(x_1, x_4, x_2, x_5, x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_7);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_withLoggedIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = 1;
x_12 = l_IO_FS_withIsolatedStreams___redArg(x_3, x_6, x_4, x_7, x_11);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lake_withLoggedIO___redArg___lam__2), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_9);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_3(x_7, lean_box(0), x_2, x_3);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_Lake_extractLog___redArg___closed__0;
x_13 = 3;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_apply_1(x_2, x_14);
x_16 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_9);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_8);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_11);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_error(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = l_Lake_extractLog___redArg___closed__0;
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_apply_1(x_4, x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_18, 0, x_11);
lean_inc(x_10);
x_19 = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_10);
x_20 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_13);
x_21 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_20, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_apply_1(x_3, x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_errorWithLog___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_11);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l_Lake_ELog_error___redArg___lam__3), 5, 4);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_10);
x_19 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_5, x_13);
x_20 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_extractLog___redArg___closed__0;
x_6 = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
lean_closure_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_monadError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_extractLog___redArg___closed__0;
x_7 = lean_alloc_closure((void*)(l_Lake_ELog_monadError___redArg___lam__4), 7, 5);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = l_Lake_extractLog___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_8);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_failure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = l_Lake_extractLog___redArg___closed__0;
x_12 = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_10);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Array_shrink___redArg(x_2, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_apply_3(x_7, lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_apply_3(x_9, lean_box(0), x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_orElse___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ELog_orElse___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_3, x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_ELog_orElse___redArg___lam__2), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_apply_3(x_7, lean_box(0), x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_extractLog___redArg___closed__0;
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(x_7, 0, x_3);
lean_inc(x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ELog_alternative(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lake_extractLog___redArg___closed__0;
lean_inc_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_ELog_failure___redArg___lam__1), 2, 1);
lean_closure_set(x_8, 0, x_4);
lean_inc(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_5);
x_9 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__2), 6, 5);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_7);
lean_closure_set(x_9, 3, x_6);
lean_closure_set(x_9, 4, x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_ELog_alternative___redArg___lam__4), 6, 3);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_6);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instMonadStateOfStateTOfMonad___redArg(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogLogTOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadLogLogTOfMonad___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_LogT_run(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_LogT_run_x27___redArg___lam__0___boxed), 1, 0);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_LogT_run_x27___redArg___lam__0___boxed), 1, 0);
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_run_x27___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LogT_run_x27___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
}
static lean_object* _init_l_Lake_LogT_takeAndRun___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_takeLog___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = l_Lake_LogT_takeAndRun___redArg___closed__0;
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_6);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = l_Lake_LogT_takeAndRun___redArg___closed__0;
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__0), 4, 3);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_10);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_10);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_takeAndRun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_LogT_takeAndRun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lake_LogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_array_get_size(x_8);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_2, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
x_13 = lean_apply_2(x_1, lean_box(0), x_11);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_9);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_10, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
x_16 = lean_apply_2(x_1, lean_box(0), x_11);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_9);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_18 = 0;
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_5, x_8, x_18, x_19, x_11);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_9);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lake_Log_empty___closed__0;
x_11 = lean_apply_1(x_4, x_10);
x_12 = lean_apply_2(x_3, lean_box(0), x_11);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_8);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lake_Log_empty___closed__0;
x_14 = lean_apply_1(x_7, x_13);
x_15 = lean_apply_2(x_6, lean_box(0), x_14);
lean_inc(x_9);
x_16 = lean_alloc_closure((void*)(l_Lake_LogT_replayLog___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_9);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_11);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_LogT_replayLog___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_LogT_replayLog___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = l_Lake_EStateT_instMonadStateOfOfPure___redArg(x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLogELogTOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadLogELogTOfMonad___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_apply_2(x_1, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_array_push(x_7, x_2);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_12 = lean_apply_2(x_1, lean_box(0), x_4);
lean_inc(x_3);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_10);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_8);
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
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1), 3, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_1);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_array_push(x_16, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_apply_2(x_1, lean_box(0), x_21);
lean_inc(x_3);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_19);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_17);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_apply_2(x_1, lean_box(0), x_4);
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
x_30 = lean_apply_2(x_1, lean_box(0), x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = 3;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
lean_inc(x_3);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_3);
lean_inc_ref(x_7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_14 = lean_apply_2(x_2, lean_box(0), x_1);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_4, x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3), 4, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_3);
lean_inc_ref(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_apply_2(x_2, lean_box(0), x_21);
x_23 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_4, x_22);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0), 1, 0);
x_7 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4), 7, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorELogTOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadErrorELogTOfMonad___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, x_2, x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_2(x_3, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_apply_2(x_3, lean_box(0), x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_1);
x_11 = l_Array_shrink___redArg(x_8, x_7);
lean_dec(x_7);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
x_12 = lean_apply_2(x_1, lean_box(0), x_4);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_10);
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
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_1);
x_18 = l_Array_shrink___redArg(x_15, x_14);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_apply_2(x_1, lean_box(0), x_19);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_17);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
lean_inc_ref(x_7);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_7);
x_11 = lean_apply_2(x_2, lean_box(0), x_1);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_3, x_11);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
lean_inc_ref(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_apply_2(x_2, lean_box(0), x_15);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_3, x_16);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_5);
return x_18;
}
}
}
static lean_object* _init_l_Lake_instAlternativeELogTOfMonad___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 4);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_dec(x_9);
x_10 = l_Lake_instAlternativeELogTOfMonad___redArg___closed__0;
lean_inc(x_3);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_3);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(x_12, 0, x_6);
lean_inc(x_3);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
lean_inc(x_3);
lean_inc(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_3);
lean_inc(x_3);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_3);
lean_inc(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_14);
lean_inc(x_6);
lean_inc_ref(x_5);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_3);
x_18 = l_Lake_EStateT_instFunctor___redArg(x_5);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_19, 0, x_6);
lean_ctor_set(x_2, 4, x_15);
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set(x_2, 2, x_17);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = l_Lake_instAlternativeELogTOfMonad___redArg___closed__0;
lean_inc(x_3);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__2), 6, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_3);
lean_inc(x_22);
x_25 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__3), 2, 1);
lean_closure_set(x_25, 0, x_22);
lean_inc(x_3);
lean_inc(x_22);
lean_inc_ref(x_21);
x_26 = lean_alloc_closure((void*)(l_Lake_instAlternativeELogTOfMonad___redArg___lam__4), 7, 5);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_22);
lean_closure_set(x_26, 2, x_23);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_25);
lean_inc(x_3);
lean_inc(x_22);
x_27 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_3);
lean_inc(x_3);
lean_inc(x_22);
x_28 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_28, 0, x_22);
lean_closure_set(x_28, 1, x_3);
lean_inc(x_22);
x_29 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_29, 0, x_22);
lean_closure_set(x_29, 1, x_27);
lean_inc(x_22);
lean_inc_ref(x_21);
x_30 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_30, 0, x_21);
lean_closure_set(x_30, 1, x_22);
lean_closure_set(x_30, 2, x_3);
x_31 = l_Lake_EStateT_instFunctor___redArg(x_21);
x_32 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_32, 0, x_22);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_28);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_24);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeELogTOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instAlternativeELogTOfMonad___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_ELogT_run_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_toExcept___boxed), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_ELogT_run_x27___redArg___closed__0;
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lake_ELogT_run_x27___redArg___closed__0;
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_ELogT_toLogT___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_toProd), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_ELogT_toLogT___redArg___closed__0;
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lake_ELogT_toLogT___redArg___closed__0;
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_ELogT_toLogT_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_toProd_x3f), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_toLogT_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_ELogT_run_x3f_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EResult_result_x3f___boxed), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_run_x3f_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_6; 
x_6 = lean_apply_2(x_1, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_array_get_size(x_13);
lean_inc(x_12);
x_15 = l_Array_extract___redArg(x_13, x_12, x_14);
x_16 = l_Array_shrink___redArg(x_13, x_12);
lean_dec(x_12);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_15);
x_17 = lean_apply_2(x_1, lean_box(0), x_4);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_array_get_size(x_20);
lean_inc(x_19);
x_22 = l_Array_extract___redArg(x_20, x_19, x_21);
x_23 = l_Array_shrink___redArg(x_20, x_19);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_apply_2(x_1, lean_box(0), x_24);
x_26 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_25, x_3);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_apply_1(x_3, x_4);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_catchLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_apply_1(x_5, x_6);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_ELogT_catchLog___redArg___lam__1), 4, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_1(x_2, x_7);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__0), 3, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_apply_1(x_2, x_12);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = l_Lake_LogT_takeAndRun___redArg___closed__0;
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_7);
lean_closure_set(x_13, 3, x_3);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_takeAndRun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = l_Lake_LogT_takeAndRun___redArg___closed__0;
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__2), 5, 4);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_10);
lean_closure_set(x_16, 3, x_6);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__3), 5, 4);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_7);
lean_closure_set(x_17, 2, x_10);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_array_get_size(x_10);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_2, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
x_15 = lean_apply_2(x_1, lean_box(0), x_13);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_11);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
x_18 = lean_apply_2(x_1, lean_box(0), x_13);
x_19 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_18, x_11);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_5, x_10, x_20, x_21, x_13);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_11);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_5);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec_ref(x_8);
x_25 = lean_array_get_size(x_24);
x_26 = lean_box(0);
x_27 = lean_nat_dec_lt(x_2, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_4);
x_28 = lean_apply_2(x_1, lean_box(0), x_26);
x_29 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_28, x_6);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_25, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_4);
x_31 = lean_apply_2(x_1, lean_box(0), x_26);
x_32 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_31, x_6);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_33 = 0;
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_7, x_24, x_33, x_34, x_26);
x_36 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_35, x_6);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 4);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lake_Log_empty___closed__0;
x_12 = lean_apply_1(x_4, x_11);
x_13 = lean_apply_2(x_3, lean_box(0), x_12);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(x_14, 0, x_7);
lean_inc_ref(x_9);
x_15 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_10);
lean_closure_set(x_15, 2, x_8);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_9);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 4);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lake_Log_empty___closed__0;
x_15 = lean_apply_1(x_7, x_14);
x_16 = lean_apply_2(x_6, lean_box(0), x_15);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__2), 2, 1);
lean_closure_set(x_17, 0, x_10);
lean_inc_ref(x_12);
x_18 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_12);
lean_closure_set(x_18, 5, x_17);
lean_closure_set(x_18, 6, x_12);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_ELogT_takeAndRun___redArg___lam__1), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_array_get_size(x_11);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_2, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_12);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_13, x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec_ref(x_3);
x_21 = lean_apply_2(x_20, lean_box(0), x_14);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_12);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_3);
x_23 = 0;
x_24 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_11, x_23, x_24, x_14);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_25, x_12);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec_ref(x_9);
x_28 = lean_array_get_size(x_27);
x_29 = lean_box(0);
x_30 = lean_nat_dec_lt(x_2, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_8);
lean_dec_ref(x_5);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec_ref(x_3);
x_32 = lean_apply_2(x_31, lean_box(0), x_29);
x_33 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_32, x_7);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_28, x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_8);
lean_dec_ref(x_5);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec_ref(x_3);
x_36 = lean_apply_2(x_35, lean_box(0), x_29);
x_37 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_36, x_7);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_3);
x_38 = 0;
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_8, x_27, x_38, x_39, x_29);
x_41 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_40, x_7);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_12, 0, x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_9);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lake_Log_empty___closed__0;
x_16 = lean_apply_1(x_5, x_15);
x_17 = lean_apply_2(x_4, lean_box(0), x_16);
lean_inc_ref(x_12);
x_18 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__4___boxed), 9, 8);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_7);
lean_closure_set(x_18, 3, x_11);
lean_closure_set(x_18, 4, x_2);
lean_closure_set(x_18, 5, x_12);
lean_closure_set(x_18, 6, x_13);
lean_closure_set(x_18, 7, x_12);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 4);
lean_inc(x_14);
lean_dec_ref(x_9);
x_15 = lean_alloc_closure((void*)(l_Lake_Log_replay___redArg___lam__0), 3, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_MonadLog_error___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_12);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lake_Log_empty___closed__0;
x_19 = lean_apply_1(x_8, x_18);
x_20 = lean_apply_2(x_7, lean_box(0), x_19);
lean_inc_ref(x_15);
x_21 = lean_alloc_closure((void*)(l_Lake_ELogT_replayLog___redArg___lam__4___boxed), 9, 8);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_17);
lean_closure_set(x_21, 2, x_10);
lean_closure_set(x_21, 3, x_14);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_15);
lean_closure_set(x_21, 6, x_16);
lean_closure_set(x_21, 7, x_15);
x_22 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_ELogT_replayLog___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ELogT_replayLog___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLogIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_io_error_to_string(x_14);
x_16 = 3;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_array_get_size(x_3);
x_19 = lean_array_push(x_3, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_io_error_to_string(x_21);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_3);
x_27 = lean_array_push(x_3, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
}
static lean_object* _init_l_Lake_instMonadLiftIOLogIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadLiftIOLogIO___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay_spec__0(x_2, x_1, x_11, x_12, x_6, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = l_Lake_OutStream_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lake_Log_empty___closed__0;
x_13 = lean_apply_2(x_1, x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_box(x_2);
x_17 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec_ref(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_18 = x_28;
x_19 = x_27;
goto block_25;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec_ref(x_14);
x_30 = lean_box(0);
x_18 = x_30;
x_19 = x_29;
goto block_25;
}
block_25:
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay(x_19, x_17, x_15);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = l_Lake_OutStream_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_8);
x_10 = l_Lake_AnsiMode_isEnabled(x_8, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lake_Log_empty___closed__0;
x_14 = lean_apply_2(x_2, x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_box(x_3);
x_18 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec_ref(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_19 = x_29;
x_20 = x_28;
goto block_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec_ref(x_15);
x_31 = lean_box(0);
x_19 = x_31;
x_20 = x_30;
goto block_26;
}
block_26:
{
lean_object* x_21; uint8_t x_22; 
x_21 = l___private_Lake_Util_Log_0__Lake_LogIO_toBaseIO_replay(x_20, x_18, x_16);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_LogIO_toBaseIO___redArg___lam__0(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_LogIO_toBaseIO___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_toBaseIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_Lake_LogIO_toBaseIO(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_LogIO_captureLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
x_8 = lean_apply_1(x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorLoggerIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = 3;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
x_7 = lean_apply_2(x_3, x_6, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lake_instMonadErrorLoggerIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorLoggerIO___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftIOLoggerIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_io_error_to_string(x_10);
x_13 = 3;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_apply_2(x_3, x_14, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
static lean_object* _init_l_Lake_instMonadLiftIOLoggerIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadLiftIOLoggerIO___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_3, x_2, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOLoggerIO___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lake_Log_empty___closed__0;
x_14 = lean_apply_2(x_5, x_13, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec_ref(x_3);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_12, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_14);
x_24 = lean_box(0);
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_20, x_25, x_26, x_24);
x_28 = lean_apply_2(x_27, x_6, x_17);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_dec_ref(x_15);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_12, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_39, x_46, x_47, x_45);
x_49 = lean_apply_2(x_48, x_6, x_37);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_38);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_14);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_14, 1);
x_59 = lean_ctor_get(x_14, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_dec_ref(x_15);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_lt(x_12, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_63 = lean_box(0);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_63);
return x_14;
}
else
{
uint8_t x_64; 
lean_free_object(x_14);
x_64 = lean_nat_dec_le(x_61, x_61);
if (x_64 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = x_58;
goto block_11;
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_box(0);
x_66 = 0;
x_67 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_3, x_60, x_66, x_67, x_65);
x_69 = lean_apply_2(x_68, x_6, x_58);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_8 = x_70;
goto block_11;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_69);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_14, 1);
lean_inc(x_75);
lean_dec(x_14);
x_76 = lean_ctor_get(x_15, 1);
lean_inc(x_76);
lean_dec_ref(x_15);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_lt(x_12, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_77, x_77);
if (x_81 == 0)
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = x_75;
goto block_11;
}
else
{
lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_box(0);
x_83 = 0;
x_84 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_85 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_3, x_76, x_83, x_84, x_82);
x_86 = lean_apply_2(x_85, x_6, x_75);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_8 = x_87;
goto block_11;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_90 = x_86;
} else {
 lean_dec_ref(x_86);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
static lean_object* _init_l_Lake_instMonadLiftLogIOLoggerIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadLiftLogIOLoggerIO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadLiftLogIOLoggerIO___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadLiftLogIOLoggerIO() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadLiftLogIOLoggerIO___lam__0), 4, 0);
x_2 = l_Lake_instMonadLiftLogIOLoggerIO___closed__1;
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadLiftLogIOLoggerIO___lam__2), 7, 3);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
lean_closure_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lake_OutStream_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = l_Lake_AnsiMode_isEnabled(x_7, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
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
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lake_OutStream_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_8);
x_10 = l_Lake_AnsiMode_isEnabled(x_8, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_2(x_2, x_14, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_LoggerIO_toBaseIO___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_toBaseIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_Lake_LoggerIO_toBaseIO(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_push(x_5, x_2);
x_8 = lean_st_ref_set(x_1, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_25; lean_object* x_26; 
x_9 = l_Lake_Log_empty___closed__0;
x_10 = lean_st_mk_ref(x_9, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_25 = lean_alloc_closure((void*)(l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_25, 0, x_11);
x_26 = lean_apply_2(x_1, x_25, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_13 = x_29;
x_14 = x_28;
goto block_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec_ref(x_26);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_30);
x_13 = x_32;
x_14 = x_31;
goto block_24;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
block_24:
{
lean_object* x_15; 
x_15 = lean_st_ref_get(x_11, x_14);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(0);
x_3 = x_17;
x_4 = x_16;
x_5 = x_18;
goto block_8;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_3 = x_20;
x_4 = x_19;
x_5 = x_13;
goto block_8;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_3 = x_20;
x_4 = x_19;
x_5 = x_23;
goto block_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LoggerIO_captureLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LoggerIO_captureLog___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_LoggerIO_captureLog___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LoggerIO_captureLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_LoggerIO_run_x3f_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Repr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EStateT(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EStateT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_reprVerbosity___closed__0____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__0____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__0____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__1____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__1____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__1____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__2____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__2____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__2____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__3____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__3____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__3____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__4____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__4____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__4____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__5____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__5____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__5____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__6____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_ = _init_l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprVerbosity___closed__7____x40_Lake_Util_Log_99018267____hygCtx___hyg_6_);
l_Lake_instReprVerbosity___closed__0 = _init_l_Lake_instReprVerbosity___closed__0();
lean_mark_persistent(l_Lake_instReprVerbosity___closed__0);
l_Lake_instReprVerbosity = _init_l_Lake_instReprVerbosity();
lean_mark_persistent(l_Lake_instReprVerbosity);
l_Lake_instOrdVerbosity___closed__0 = _init_l_Lake_instOrdVerbosity___closed__0();
lean_mark_persistent(l_Lake_instOrdVerbosity___closed__0);
l_Lake_instOrdVerbosity = _init_l_Lake_instOrdVerbosity();
lean_mark_persistent(l_Lake_instOrdVerbosity);
l_Lake_instLTVerbosity = _init_l_Lake_instLTVerbosity();
lean_mark_persistent(l_Lake_instLTVerbosity);
l_Lake_instLEVerbosity = _init_l_Lake_instLEVerbosity();
lean_mark_persistent(l_Lake_instLEVerbosity);
l_Lake_instMinVerbosity = _init_l_Lake_instMinVerbosity();
lean_mark_persistent(l_Lake_instMinVerbosity);
l_Lake_instMaxVerbosity = _init_l_Lake_instMaxVerbosity();
lean_mark_persistent(l_Lake_instMaxVerbosity);
l_Lake_instInhabitedVerbosity = _init_l_Lake_instInhabitedVerbosity();
l_Lake_AnsiMode_noConfusion___redArg___closed__0 = _init_l_Lake_AnsiMode_noConfusion___redArg___closed__0();
lean_mark_persistent(l_Lake_AnsiMode_noConfusion___redArg___closed__0);
l_Lake_reprAnsiMode___closed__0____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_ = _init_l_Lake_reprAnsiMode___closed__0____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprAnsiMode___closed__0____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_);
l_Lake_reprAnsiMode___closed__1____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_ = _init_l_Lake_reprAnsiMode___closed__1____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprAnsiMode___closed__1____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_);
l_Lake_reprAnsiMode___closed__2____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_ = _init_l_Lake_reprAnsiMode___closed__2____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprAnsiMode___closed__2____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_);
l_Lake_reprAnsiMode___closed__3____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_ = _init_l_Lake_reprAnsiMode___closed__3____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprAnsiMode___closed__3____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_);
l_Lake_reprAnsiMode___closed__4____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_ = _init_l_Lake_reprAnsiMode___closed__4____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprAnsiMode___closed__4____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_);
l_Lake_reprAnsiMode___closed__5____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_ = _init_l_Lake_reprAnsiMode___closed__5____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_();
lean_mark_persistent(l_Lake_reprAnsiMode___closed__5____x40_Lake_Util_Log_2259154522____hygCtx___hyg_6_);
l_Lake_instReprAnsiMode___closed__0 = _init_l_Lake_instReprAnsiMode___closed__0();
lean_mark_persistent(l_Lake_instReprAnsiMode___closed__0);
l_Lake_instReprAnsiMode = _init_l_Lake_instReprAnsiMode();
lean_mark_persistent(l_Lake_instReprAnsiMode);
l_Lake_Ansi_chalk___closed__0 = _init_l_Lake_Ansi_chalk___closed__0();
lean_mark_persistent(l_Lake_Ansi_chalk___closed__0);
l_Lake_Ansi_chalk___closed__1 = _init_l_Lake_Ansi_chalk___closed__1();
lean_mark_persistent(l_Lake_Ansi_chalk___closed__1);
l_Lake_Ansi_chalk___closed__2 = _init_l_Lake_Ansi_chalk___closed__2();
lean_mark_persistent(l_Lake_Ansi_chalk___closed__2);
l_Lake_instCoeStreamOutStream = _init_l_Lake_instCoeStreamOutStream();
lean_mark_persistent(l_Lake_instCoeStreamOutStream);
l_Lake_instCoeHandleOutStream = _init_l_Lake_instCoeHandleOutStream();
lean_mark_persistent(l_Lake_instCoeHandleOutStream);
l_Lake_instInhabitedLogLevel = _init_l_Lake_instInhabitedLogLevel();
l_Lake_reprLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_reprLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_ = _init_l_Lake_reprLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_();
lean_mark_persistent(l_Lake_reprLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_9_);
l_Lake_instReprLogLevel___closed__0 = _init_l_Lake_instReprLogLevel___closed__0();
lean_mark_persistent(l_Lake_instReprLogLevel___closed__0);
l_Lake_instReprLogLevel = _init_l_Lake_instReprLogLevel();
lean_mark_persistent(l_Lake_instReprLogLevel);
l_Lake_instOrdLogLevel___closed__0 = _init_l_Lake_instOrdLogLevel___closed__0();
lean_mark_persistent(l_Lake_instOrdLogLevel___closed__0);
l_Lake_instOrdLogLevel = _init_l_Lake_instOrdLogLevel();
lean_mark_persistent(l_Lake_instOrdLogLevel);
l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__3____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__4____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__5____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__6____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_toJsonLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_ = _init_l_Lake_toJsonLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_();
lean_mark_persistent(l_Lake_toJsonLogLevel___closed__7____x40_Lake_Util_Log_328358094____hygCtx___hyg_36_);
l_Lake_instToJsonLogLevel___closed__0 = _init_l_Lake_instToJsonLogLevel___closed__0();
lean_mark_persistent(l_Lake_instToJsonLogLevel___closed__0);
l_Lake_instToJsonLogLevel = _init_l_Lake_instToJsonLogLevel();
lean_mark_persistent(l_Lake_instToJsonLogLevel);
l_Lake_fromJsonLogLevel___lam__0___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___lam__0___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___lam__0___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___lam__0___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___lam__0___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___lam__0___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___lam__1___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___lam__1___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___lam__1___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___lam__2___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___lam__2___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___lam__2___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___lam__3___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___lam__3___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___lam__3___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___closed__0____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___closed__1____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_fromJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_ = _init_l_Lake_fromJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_();
lean_mark_persistent(l_Lake_fromJsonLogLevel___closed__2____x40_Lake_Util_Log_328358094____hygCtx___hyg_46_);
l_Lake_instFromJsonLogLevel___closed__0 = _init_l_Lake_instFromJsonLogLevel___closed__0();
lean_mark_persistent(l_Lake_instFromJsonLogLevel___closed__0);
l_Lake_instFromJsonLogLevel = _init_l_Lake_instFromJsonLogLevel();
lean_mark_persistent(l_Lake_instFromJsonLogLevel);
l_Lake_instLTLogLevel = _init_l_Lake_instLTLogLevel();
lean_mark_persistent(l_Lake_instLTLogLevel);
l_Lake_instLELogLevel = _init_l_Lake_instLELogLevel();
lean_mark_persistent(l_Lake_instLELogLevel);
l_Lake_instMinLogLevel = _init_l_Lake_instMinLogLevel();
lean_mark_persistent(l_Lake_instMinLogLevel);
l_Lake_instMaxLogLevel = _init_l_Lake_instMaxLogLevel();
lean_mark_persistent(l_Lake_instMaxLogLevel);
l_Lake_LogLevel_ansiColor___closed__0 = _init_l_Lake_LogLevel_ansiColor___closed__0();
lean_mark_persistent(l_Lake_LogLevel_ansiColor___closed__0);
l_Lake_LogLevel_ansiColor___closed__1 = _init_l_Lake_LogLevel_ansiColor___closed__1();
lean_mark_persistent(l_Lake_LogLevel_ansiColor___closed__1);
l_Lake_LogLevel_ansiColor___closed__2 = _init_l_Lake_LogLevel_ansiColor___closed__2();
lean_mark_persistent(l_Lake_LogLevel_ansiColor___closed__2);
l_Lake_LogLevel_ofString_x3f___closed__0 = _init_l_Lake_LogLevel_ofString_x3f___closed__0();
lean_mark_persistent(l_Lake_LogLevel_ofString_x3f___closed__0);
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
l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0 = _init_l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0);
l___private_Lake_Util_Log_0__Lake_instToStringLogLevel = _init_l___private_Lake_Util_Log_0__Lake_instToStringLogLevel();
lean_mark_persistent(l___private_Lake_Util_Log_0__Lake_instToStringLogLevel);
l_Lake_instInhabitedLogEntry___closed__0 = _init_l_Lake_instInhabitedLogEntry___closed__0();
lean_mark_persistent(l_Lake_instInhabitedLogEntry___closed__0);
l_Lake_instInhabitedLogEntry___closed__1 = _init_l_Lake_instInhabitedLogEntry___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLogEntry___closed__1);
l_Lake_instInhabitedLogEntry = _init_l_Lake_instInhabitedLogEntry();
lean_mark_persistent(l_Lake_instInhabitedLogEntry);
l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_ = _init_l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_();
lean_mark_persistent(l_Lake_toJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_);
l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_ = _init_l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_();
lean_mark_persistent(l_Lake_toJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_);
l_Lake_toJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_ = _init_l_Lake_toJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_();
lean_mark_persistent(l_Lake_toJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_27_);
l_Lake_instToJsonLogEntry___closed__0 = _init_l_Lake_instToJsonLogEntry___closed__0();
lean_mark_persistent(l_Lake_instToJsonLogEntry___closed__0);
l_Lake_instToJsonLogEntry = _init_l_Lake_instToJsonLogEntry();
lean_mark_persistent(l_Lake_instToJsonLogEntry);
l_Lake_fromJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__0____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__1____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__2____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__3____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__3____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__3____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__4____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__4____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__4____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__5____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__6____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__6____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__6____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__7____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__7____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__7____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__8____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__8____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__8____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__9____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__10____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__11____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__11____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__11____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__12____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__12____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__12____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__13____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__13____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__13____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_ = _init_l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_();
lean_mark_persistent(l_Lake_fromJsonLogEntry___closed__14____x40_Lake_Util_Log_2045950852____hygCtx___hyg_37_);
l_Lake_instFromJsonLogEntry___closed__0 = _init_l_Lake_instFromJsonLogEntry___closed__0();
lean_mark_persistent(l_Lake_instFromJsonLogEntry___closed__0);
l_Lake_instFromJsonLogEntry = _init_l_Lake_instFromJsonLogEntry();
lean_mark_persistent(l_Lake_instFromJsonLogEntry);
l_Lake_LogEntry_toString___closed__0 = _init_l_Lake_LogEntry_toString___closed__0();
lean_mark_persistent(l_Lake_LogEntry_toString___closed__0);
l_Lake_LogEntry_toString___closed__1 = _init_l_Lake_LogEntry_toString___closed__1();
lean_mark_persistent(l_Lake_LogEntry_toString___closed__1);
l_Lake_instToStringLogEntry = _init_l_Lake_instToStringLogEntry();
lean_mark_persistent(l_Lake_instToStringLogEntry);
l_Lake_LogEntry_ofSerialMessage___closed__0 = _init_l_Lake_LogEntry_ofSerialMessage___closed__0();
lean_mark_persistent(l_Lake_LogEntry_ofSerialMessage___closed__0);
l_Lake_instInhabitedLog___closed__0 = _init_l_Lake_instInhabitedLog___closed__0();
lean_mark_persistent(l_Lake_instInhabitedLog___closed__0);
l_Lake_instInhabitedLog = _init_l_Lake_instInhabitedLog();
lean_mark_persistent(l_Lake_instInhabitedLog);
l_Lake_instToJsonLog = _init_l_Lake_instToJsonLog();
lean_mark_persistent(l_Lake_instToJsonLog);
l_Lake_instFromJsonLog = _init_l_Lake_instFromJsonLog();
lean_mark_persistent(l_Lake_instFromJsonLog);
l_Lake_Log_instInhabitedPos = _init_l_Lake_Log_instInhabitedPos();
lean_mark_persistent(l_Lake_Log_instInhabitedPos);
l_Lake_instOfNatPos = _init_l_Lake_instOfNatPos();
lean_mark_persistent(l_Lake_instOfNatPos);
l_Lake_instOrdPos = _init_l_Lake_instOrdPos();
lean_mark_persistent(l_Lake_instOrdPos);
l_Lake_instLTPos = _init_l_Lake_instLTPos();
lean_mark_persistent(l_Lake_instLTPos);
l_Lake_instLEPos = _init_l_Lake_instLEPos();
lean_mark_persistent(l_Lake_instLEPos);
l_Lake_instMinPos = _init_l_Lake_instMinPos();
lean_mark_persistent(l_Lake_instMinPos);
l_Lake_instMaxPos = _init_l_Lake_instMaxPos();
lean_mark_persistent(l_Lake_instMaxPos);
l_Lake_Log_empty___closed__0 = _init_l_Lake_Log_empty___closed__0();
lean_mark_persistent(l_Lake_Log_empty___closed__0);
l_Lake_Log_empty = _init_l_Lake_Log_empty();
lean_mark_persistent(l_Lake_Log_empty);
l_Lake_Log_instEmptyCollection = _init_l_Lake_Log_instEmptyCollection();
lean_mark_persistent(l_Lake_Log_instEmptyCollection);
l_Lake_Log_instAppend___closed__0 = _init_l_Lake_Log_instAppend___closed__0();
lean_mark_persistent(l_Lake_Log_instAppend___closed__0);
l_Lake_Log_instAppend = _init_l_Lake_Log_instAppend();
lean_mark_persistent(l_Lake_Log_instAppend);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Log_toString_spec__0___closed__0);
l_Lake_Log_instToString___closed__0 = _init_l_Lake_Log_instToString___closed__0();
lean_mark_persistent(l_Lake_Log_instToString___closed__0);
l_Lake_Log_instToString = _init_l_Lake_Log_instToString();
lean_mark_persistent(l_Lake_Log_instToString);
l_Lake_Log_filter___closed__0 = _init_l_Lake_Log_filter___closed__0();
lean_mark_persistent(l_Lake_Log_filter___closed__0);
l_Lake_Log_filter___closed__1 = _init_l_Lake_Log_filter___closed__1();
lean_mark_persistent(l_Lake_Log_filter___closed__1);
l_Lake_Log_filter___closed__2 = _init_l_Lake_Log_filter___closed__2();
lean_mark_persistent(l_Lake_Log_filter___closed__2);
l_Lake_Log_filter___closed__3 = _init_l_Lake_Log_filter___closed__3();
lean_mark_persistent(l_Lake_Log_filter___closed__3);
l_Lake_Log_filter___closed__4 = _init_l_Lake_Log_filter___closed__4();
lean_mark_persistent(l_Lake_Log_filter___closed__4);
l_Lake_Log_filter___closed__5 = _init_l_Lake_Log_filter___closed__5();
lean_mark_persistent(l_Lake_Log_filter___closed__5);
l_Lake_Log_filter___closed__6 = _init_l_Lake_Log_filter___closed__6();
lean_mark_persistent(l_Lake_Log_filter___closed__6);
l_Lake_Log_filter___closed__7 = _init_l_Lake_Log_filter___closed__7();
lean_mark_persistent(l_Lake_Log_filter___closed__7);
l_Lake_Log_filter___closed__8 = _init_l_Lake_Log_filter___closed__8();
lean_mark_persistent(l_Lake_Log_filter___closed__8);
l_Lake_Log_filter___closed__9 = _init_l_Lake_Log_filter___closed__9();
lean_mark_persistent(l_Lake_Log_filter___closed__9);
l_Lake_extractLog___redArg___closed__0 = _init_l_Lake_extractLog___redArg___closed__0();
lean_mark_persistent(l_Lake_extractLog___redArg___closed__0);
l_Lake_withLoggedIO___redArg___lam__2___closed__0 = _init_l_Lake_withLoggedIO___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lake_withLoggedIO___redArg___lam__2___closed__0);
l_Lake_withLoggedIO___redArg___lam__2___closed__1 = _init_l_Lake_withLoggedIO___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lake_withLoggedIO___redArg___lam__2___closed__1);
l_Lake_LogT_takeAndRun___redArg___closed__0 = _init_l_Lake_LogT_takeAndRun___redArg___closed__0();
lean_mark_persistent(l_Lake_LogT_takeAndRun___redArg___closed__0);
l_Lake_instAlternativeELogTOfMonad___redArg___closed__0 = _init_l_Lake_instAlternativeELogTOfMonad___redArg___closed__0();
lean_mark_persistent(l_Lake_instAlternativeELogTOfMonad___redArg___closed__0);
l_Lake_ELogT_run_x27___redArg___closed__0 = _init_l_Lake_ELogT_run_x27___redArg___closed__0();
lean_mark_persistent(l_Lake_ELogT_run_x27___redArg___closed__0);
l_Lake_ELogT_toLogT___redArg___closed__0 = _init_l_Lake_ELogT_toLogT___redArg___closed__0();
lean_mark_persistent(l_Lake_ELogT_toLogT___redArg___closed__0);
l_Lake_ELogT_toLogT_x3f___redArg___closed__0 = _init_l_Lake_ELogT_toLogT_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_ELogT_toLogT_x3f___redArg___closed__0);
l_Lake_ELogT_run_x3f_x27___redArg___closed__0 = _init_l_Lake_ELogT_run_x3f_x27___redArg___closed__0();
lean_mark_persistent(l_Lake_ELogT_run_x3f_x27___redArg___closed__0);
l_Lake_instMonadLiftIOLogIO = _init_l_Lake_instMonadLiftIOLogIO();
lean_mark_persistent(l_Lake_instMonadLiftIOLogIO);
l_Lake_instMonadErrorLoggerIO = _init_l_Lake_instMonadErrorLoggerIO();
lean_mark_persistent(l_Lake_instMonadErrorLoggerIO);
l_Lake_instMonadLiftIOLoggerIO = _init_l_Lake_instMonadLiftIOLoggerIO();
lean_mark_persistent(l_Lake_instMonadLiftIOLoggerIO);
l_Lake_instMonadLiftLogIOLoggerIO___closed__0 = _init_l_Lake_instMonadLiftLogIOLoggerIO___closed__0();
lean_mark_persistent(l_Lake_instMonadLiftLogIOLoggerIO___closed__0);
l_Lake_instMonadLiftLogIOLoggerIO___closed__1 = _init_l_Lake_instMonadLiftLogIOLoggerIO___closed__1();
lean_mark_persistent(l_Lake_instMonadLiftLogIOLoggerIO___closed__1);
l_Lake_instMonadLiftLogIOLoggerIO = _init_l_Lake_instMonadLiftLogIOLoggerIO();
lean_mark_persistent(l_Lake_instMonadLiftLogIOLoggerIO);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
