// Lean compiler output
// Module: Init.System.IO
// Imports: Init.Control.EState Init.Control.Reader Init.Data.String Init.Data.ByteArray Init.System.IOError Init.System.FilePath Init.System.ST Init.Data.ToString.Macro Init.Data.Ord
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_Buffer_pos___default;
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion(lean_object*);
static lean_object* l_IO_FS_instReprMetadata___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3___boxed(lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122_(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__23;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mkPrim___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__7;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
lean_object* lean_chmod(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runEval(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__12;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__6;
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2234_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2(lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2163_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FileRight_user___default___closed__1;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__14;
LEAN_EXPORT lean_object* l_Lean_instEval___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18;
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13;
static lean_object* l_Lean_instEvalUnit___rarg___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__1;
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__17;
LEAN_EXPORT lean_object* l_unsafeIO___rarg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__3;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
LEAN_EXPORT lean_object* l_IO_print(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__5(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
LEAN_EXPORT lean_object* l_Lean_instEvalUnit(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime;
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__14;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_user___default;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines_read___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__6;
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_IO_FS_instReprSystemTime___closed__1;
extern lean_object* l_Lean_interpolatedStrKind;
LEAN_EXPORT lean_object* l_IO_Process_SpawnArgs_args___default;
static uint32_t l_IO_AccessRight_flags___closed__6;
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__21;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__5;
LEAN_EXPORT lean_object* lean_io_eprint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__13;
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_SpawnArgs_cwd___default;
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval__1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__13;
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instEvalUnit___rarg___closed__2;
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__19;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__14;
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedSystemTime___closed__1;
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_runEval___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__12;
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata;
static lean_object* l_termPrintln_x21_______closed__5;
LEAN_EXPORT lean_object* l_IO_eprint___rarg(lean_object*, lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__8;
lean_object* l_Int_repr(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12;
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__3;
LEAN_EXPORT lean_object* l_IO_lazyPure___rarg(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__15;
static lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__2;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask(lean_object*);
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___closed__2;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___closed__1;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__2;
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361_(lean_object*, lean_object*);
static lean_object* l_IO_appDir___closed__1;
LEAN_EXPORT lean_object* l_IO_appDir(lean_object*);
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___rarg(lean_object*, lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__1;
static uint32_t l_IO_AccessRight_flags___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1(lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__9;
LEAN_EXPORT lean_object* l_IO_Process_SpawnArgs_env___default;
LEAN_EXPORT lean_object* l_IO_FS_instLTSystemTime;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946_(uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_dedicated;
LEAN_EXPORT lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
static lean_object* l_IO_FS_instInhabitedStream___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__4;
static lean_object* l_IO_FS_instInhabitedSystemTime___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__24;
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43;
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__7;
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__26;
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
static lean_object* l_termPrintln_x21_______closed__9;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___closed__4;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO;
static lean_object* l_termPrintln_x21_______closed__16;
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__3;
lean_object* lean_io_remove_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__6;
LEAN_EXPORT lean_object* l_IO_eprintln___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__11;
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Process_run___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion(lean_object*);
static lean_object* l_IO_FS_instBEqSystemTime___closed__1;
uint32_t l_String_back(lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_runEval___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__20;
LEAN_EXPORT lean_object* l_IO_eprint(lean_object*);
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___rarg(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__10;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__9;
lean_object* l_EStateM_instMonadFinallyEStateM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__4;
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime;
lean_object* lean_byte_array_size(lean_object*);
static lean_object* l_termPrintln_x21_______closed__10;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2163____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__8;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines_read(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__2;
static lean_object* l_termPrintln_x21_______closed__2;
static lean_object* l_IO_FS_instReprFileType___closed__1;
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4;
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__8;
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_runEval___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5___boxed(lean_object*, lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
static lean_object* l_instMonadExceptOfEIO___closed__1;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__4;
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__1(lean_object*);
lean_object* lean_io_prim_handle_is_eof(lean_object*, lean_object*);
static lean_object* l_IO_Process_run___closed__2;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__7;
LEAN_EXPORT lean_object* l_IO_FS_Stream_Buffer_data___default;
static lean_object* l_IO_FS_instReprDirEntry___closed__1;
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__11;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2234____boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO;
lean_object* lean_io_has_finished(lean_object*, lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runEval___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__1;
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__3;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_termPrintln_x21____;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2(lean_object*, lean_object*);
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AccessRight_write___default;
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream;
static lean_object* l_termPrintln_x21_______closed__13;
LEAN_EXPORT lean_object* l_IO_ofExcept___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__25;
LEAN_EXPORT lean_object* l_BaseIO_toIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__5;
LEAN_EXPORT uint8_t l_IO_Process_StdioConfig_stdout___default;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33;
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
static lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__1;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__11;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_object* l_EStateM_nonBacktrackable(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_io_check_canceled(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4(lean_object*, size_t, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
lean_object* lean_io_current_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO___rarg(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__12;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime;
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___rarg(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__11;
lean_object* l_String_quote(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
static lean_object* l_IO_withStdin___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instBEqFileType___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2(size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_instInhabitedStream___lambda__1___closed__2;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22;
lean_object* l_EStateM_instMonadExceptOfEStateM___rarg(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType;
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_instMonadFinallyEIO___closed__1;
LEAN_EXPORT lean_object* l_IO_FileRight_other___default;
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__6;
LEAN_EXPORT lean_object* l_unsafeIO(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
LEAN_EXPORT lean_object* l_IO_iterate___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_instOrdSystemTime___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__4;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__17;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40;
LEAN_EXPORT lean_object* l_IO_FS_instLESystemTime;
LEAN_EXPORT lean_object* l_IO_FileRight_group___default;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__11;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__2;
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_IO_FS_instInhabitedStream___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3;
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval__1___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___rarg(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6;
lean_object* l_EStateM_instInhabitedEStateM___rarg(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__10;
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6;
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
static uint32_t l_IO_AccessRight_flags___closed__10;
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__8;
static lean_object* l_IO_appDir___closed__2;
lean_object* l_ByteArray_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__2;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__4;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__7;
static uint32_t l_IO_FS_instInhabitedStream___lambda__1___closed__1;
static lean_object* l_instMonadEIO___closed__1;
uint32_t lean_uint32_lor(uint32_t, uint32_t);
lean_object* lean_io_app_path(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
lean_object* lean_io_initializing(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__6___boxed(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41;
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1(lean_object*, lean_object*);
static lean_object* l_IO_FS_Mode_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_Process_StdioConfig_stderr___default;
uint8_t lean_byte_array_get(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_isEof___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__8;
LEAN_EXPORT uint8_t l_IO_Process_StdioConfig_stdin___default;
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___rarg(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__9;
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__12;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__13;
LEAN_EXPORT lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_lines___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__6(lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__1;
LEAN_EXPORT lean_object* l_IO_iterate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO(lean_object*);
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__17;
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runEval___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__4;
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AccessRight_execution___default;
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
LEAN_EXPORT lean_object* l_Lean_instEvalIO(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__15;
LEAN_EXPORT lean_object* l_IO_withStdout___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__14;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__18;
lean_object* lean_uint32_to_nat(uint32_t);
static uint32_t l_IO_AccessRight_flags___closed__5;
LEAN_EXPORT lean_object* l_IO_withStdout___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_ofBuffer___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2;
static lean_object* l_termPrintln_x21_______closed__8;
lean_object* lean_task_get_own(lean_object*);
static uint32_t l_IO_AccessRight_flags___closed__7;
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object*, lean_object*);
static lean_object* l_termPrintln_x21_______closed__1;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1;
static uint32_t l_IO_AccessRight_flags___closed__3;
static lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__5;
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__7;
lean_object* lean_io_create_dir(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2;
LEAN_EXPORT uint8_t l_IO_AccessRight_read___default;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* _init_l_instMonadEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadEIO___closed__1;
return x_2;
}
}
static lean_object* _init_l_instMonadFinallyEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonadFinallyEStateM), 4, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadFinallyEIO___closed__1;
return x_2;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_nonBacktrackable(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadExceptOfEIO___closed__1;
x_2 = l_EStateM_instMonadExceptOfEStateM___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadExceptOfEIO___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_2, x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_orElse___at_instOrElseEIO___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orElse___at_instOrElseEIO___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabitedEStateM___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instInhabitedEIO___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_instMonadBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMonadFinallyBaseIO() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadFinallyEIO___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BaseIO_toEIO___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_catchExceptions___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BaseIO_toIO___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toIO___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toIO_x27___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_toEIO___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unsafeBaseIO___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_unsafeEIO___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unsafeIO___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_timeit(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_allocprof(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_initializing(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_as_task(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_map_task(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_bind_task(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_BaseIO_mapTasks_go___rarg(x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_List_reverse___rarg(x_4);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_io_as_task(x_7, x_2, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_BaseIO_mapTasks_go___rarg___lambda__1), 6, 4);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_io_bind_task(x_9, x_11, x_2, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BaseIO_mapTasks_go___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_BaseIO_mapTasks_go___rarg(x_1, x_3, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BaseIO_mapTasks___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_io_as_task(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_asTask___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_io_map_task(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_task_pure(x_11);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_task_pure(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_bindTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_io_bind_task(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_bindTask___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_BaseIO_mapTasks___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EIO_mapTasks___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_ofExcept___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_lazyPure___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_mono_ms_now(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_mono_nanos_now(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_io_get_random_bytes(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_sleep___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_dbg_sleep(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_sleep___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_IO_sleep(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_io_as_task(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_asTask___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_io_map_task(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_mapTask___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_bindTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_io_bind_task(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_bindTask___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_EIO_mapTask___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_BaseIO_mapTasks___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_mapTasks___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_check_canceled(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_cancel(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_has_finished(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait_any(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_get_num_heartbeats(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_FS_Mode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Mode_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_Mode_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Mode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Mode_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_FS_Mode_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_Mode_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint32_t _init_l_IO_FS_instInhabitedStream___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___lambda__1___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_IO_FS_instInhabitedStream___lambda__1___closed__1;
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_FS_instInhabitedStream___lambda__1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__3;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__3;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instInhabitedStream___lambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_FS_instInhabitedStream___closed__1;
x_2 = l_IO_FS_instInhabitedStream___closed__2;
x_3 = l_IO_FS_instInhabitedStream___closed__3;
x_4 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_1);
lean_ctor_set(x_4, 5, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instInhabitedStream() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedStream___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_IO_FS_instInhabitedStream___lambda__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_instInhabitedStream___lambda__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdout(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stderr(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdin(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdout(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stderr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_1 = x_7;
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_iterate___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("r");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("t");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("b");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("w");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("r+");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12;
x_2 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__3;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__5;
return x_4;
}
}
case 1:
{
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__7;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__8;
return x_6;
}
}
case 2:
{
if (x_2 == 0)
{
lean_object* x_7; 
x_7 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__10;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__11;
return x_8;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__13;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__14;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mkPrim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_mk(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags(x_2, x_3);
x_6 = lean_io_prim_handle_mk(x_1, x_5, x_4);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_FS_Handle_mk(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_read(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_file(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_create_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_current_dir(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_IO_FS_Handle_mk(x_1, x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withFile___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_withFile___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 10;
x_5 = lean_string_push(x_2, x_4);
x_6 = lean_io_prim_handle_put_str(x_1, x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_putStrLn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = 1024;
x_5 = lean_io_prim_handle_read(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_ByteArray_isEmpty(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_5);
x_10 = l_ByteArray_append(x_2, x_7);
lean_dec(x_7);
x_2 = x_10;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_ByteArray_isEmpty(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_ByteArray_append(x_2, x_12);
lean_dec(x_12);
x_2 = x_15;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readBinToEnd_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_ByteArray_empty;
x_4 = l_IO_FS_Handle_readBinToEnd_loop(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readBinToEnd(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_get_line(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_String_isEmpty(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_4);
x_9 = lean_string_append(x_2, x_6);
lean_dec(x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = l_String_isEmpty(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_string_append(x_2, x_11);
lean_dec(x_11);
x_2 = x_14;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readToEnd_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_4 = l_IO_FS_Handle_readToEnd_loop(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = 0;
x_4 = 1;
x_5 = l_IO_FS_Handle_mk(x_1, x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_ByteArray_empty;
x_9 = l_IO_FS_Handle_readBinToEnd_loop(x_6, x_8, x_7);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = 0;
x_4 = 0;
x_5 = l_IO_FS_Handle_mk(x_1, x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_9 = l_IO_FS_Handle_readToEnd_loop(x_6, x_8, x_7);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines_read(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_get_line(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_length(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = l_String_back(x_6);
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_2, x_6);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_String_dropRight(x_6, x_15);
x_17 = l_System_Platform_isWindows;
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_push(x_2, x_16);
x_2 = x_18;
x_3 = x_7;
goto _start;
}
else
{
uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_20 = l_String_back(x_16);
x_21 = 13;
x_22 = lean_uint32_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_array_push(x_2, x_16);
x_2 = x_23;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_String_dropRight(x_16, x_15);
x_26 = lean_array_push(x_2, x_25);
x_2 = x_26;
x_3 = x_7;
goto _start;
}
}
}
}
else
{
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_string_length(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
uint32_t x_33; uint32_t x_34; uint8_t x_35; 
x_33 = l_String_back(x_28);
x_34 = 10;
x_35 = lean_uint32_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_array_push(x_2, x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_String_dropRight(x_28, x_38);
x_40 = l_System_Platform_isWindows;
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_array_push(x_2, x_39);
x_2 = x_41;
x_3 = x_29;
goto _start;
}
else
{
uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_43 = l_String_back(x_39);
x_44 = 13;
x_45 = lean_uint32_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_array_push(x_2, x_39);
x_2 = x_46;
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_String_dropRight(x_39, x_38);
x_49 = lean_array_push(x_2, x_48);
x_2 = x_49;
x_3 = x_29;
goto _start;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_28);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_29);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_4);
if (x_52 == 0)
{
return x_4;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_lines_read(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_IO_FS_lines___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = 0;
x_4 = 0;
x_5 = l_IO_FS_Handle_mk(x_1, x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_lines___closed__1;
x_9 = l_IO_FS_lines_read(x_6, x_8, x_7);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_lines(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = 1;
x_5 = 1;
x_6 = l_IO_FS_Handle_mk(x_1, x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_prim_handle_write(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeBinFile(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = 1;
x_5 = 0;
x_6 = l_IO_FS_Handle_mk(x_1, x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_prim_handle_put_str(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeFile(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 10;
x_6 = lean_string_push(x_2, x_5);
x_7 = lean_apply_2(x_4, x_6, x_3);
return x_7;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("root");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("FilePath.mk ");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fileName");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{ ");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__14;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" }");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_String_quote(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__8;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Repr_addAppParen(x_7, x_8);
x_10 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__6;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__12;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
x_21 = l_String_quote(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18;
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15;
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = 0;
x_31 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
return x_31;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprDirEntry___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_FS_FileType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Mode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_FileType_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_FileType_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO.FS.FileType.dir");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO.FS.FileType.file");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO.FS.FileType.symlink");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO.FS.FileType.other");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6;
x_2 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__26() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__25;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946_(uint8_t x_1, lean_object* x_2) {
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
x_5 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__8;
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
x_11 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__14;
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
x_17 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__20;
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
x_23 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__24;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__26;
x_26 = l_Repr_addAppParen(x_25, x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instReprFileType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprFileType() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprFileType___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_IO_FS_FileType_toCtorIdx(x_1);
x_4 = l_IO_FS_FileType_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instBEqFileType() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instBEqFileType___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sec");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nsec");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Int_repr(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__4;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_17 = lean_uint32_to_nat(x_16);
x_18 = l_Nat_repr(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15;
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = 0;
x_28 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprSystemTime___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2163_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint32(x_2, sizeof(void*)*1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_uint32_dec_eq(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2163____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2163_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_2163____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instBEqSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instBEqSystemTime___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2234_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint32(x_2, sizeof(void*)*1);
x_7 = lean_int_dec_lt(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_int_dec_eq(x_3, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_uint32_dec_lt(x_4, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_uint32_dec_eq(x_4, x_6);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 2;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2234____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2234_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_2234____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instOrdSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instOrdSystemTime___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_IO_FS_instInhabitedSystemTime___closed__1;
x_2 = l_IO_FS_instInhabitedStream___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instInhabitedSystemTime___closed__2;
return x_1;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("accessed");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__3;
x_2 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modified");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("byteSize");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type");
return x_1;
}
}
static lean_object* _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122_(x_3, x_4);
x_6 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__4;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122_(x_16, x_4);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
x_21 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__8;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_25 = lean_uint64_to_nat(x_24);
x_26 = l_Nat_repr(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
x_31 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__10;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_14);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_35 = l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946_(x_34, x_4);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18;
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15;
x_42 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = 0;
x_44 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
return x_44;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_instReprMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprMetadata___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_read_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 8);
lean_dec(x_5);
x_7 = 0;
x_8 = l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087_(x_6, x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*2 + 8);
lean_dec(x_10);
x_13 = 0;
x_14 = l___private_Init_System_IO_0__IO_FS_beqFileType____x40_Init_System_IO___hyg_2087_(x_12, x_13);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_dec(x_18);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = 1;
x_7 = lean_box(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
x_21 = lean_array_uget(x_3, x_5);
x_22 = l_IO_FS_DirEntry_path(x_21);
lean_inc(x_22);
x_23 = lean_array_push(x_7, x_22);
x_24 = lean_io_metadata(x_22, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*2 + 8);
lean_dec(x_25);
x_27 = lean_box(x_26);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_inc(x_1);
x_29 = l_System_FilePath_walkDir_go(x_1, x_22, x_23, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_30, 0, x_34);
x_9 = x_30;
x_10 = x_31;
goto block_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_9 = x_37;
x_10 = x_31;
goto block_17;
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_io_realpath(x_22, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_System_FilePath_isDir(x_44, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_44);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_23);
x_9 = x_51;
x_10 = x_49;
goto block_17;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
lean_inc(x_1);
lean_inc(x_2);
x_53 = lean_apply_2(x_1, x_2, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_23);
x_9 = x_58;
x_10 = x_56;
goto block_17;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
lean_inc(x_1);
x_60 = l_System_FilePath_walkDir_go(x_1, x_44, x_23, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
lean_ctor_set(x_61, 0, x_65);
x_9 = x_61;
x_10 = x_62;
goto block_17;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_9 = x_68;
x_10 = x_62;
goto block_17;
}
}
else
{
uint8_t x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_60);
if (x_69 == 0)
{
return x_60;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_60, 0);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_60);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_44);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_53);
if (x_73 == 0)
{
return x_53;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_53, 0);
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_53);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_43);
if (x_77 == 0)
{
return x_43;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_43, 0);
x_79 = lean_ctor_get(x_43, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_43);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_27);
lean_dec(x_22);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
lean_dec(x_24);
x_82 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_23);
x_9 = x_83;
x_10 = x_81;
goto block_17;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_24);
if (x_84 == 0)
{
return x_24;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_24, 0);
x_86 = lean_ctor_get(x_24, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_24);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_13;
x_7 = x_12;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_read_dir(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(x_2, x_1, x_7, x_10, x_11, x_12, x_4, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
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
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_2);
x_5 = lean_apply_2(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = l_System_FilePath_walkDir_go___lambda__1(x_2, x_1, x_17, x_3, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_System_FilePath_walkDir_go___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_FS_lines___closed__1;
x_5 = l_System_FilePath_walkDir_go(x_2, x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
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
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_IO_withStdin___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_IO_withStdin___rarg___lambda__3___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__3), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_withStdin___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_withStdin___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_withStdin___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_IO_withStdin___rarg___lambda__3___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_withStdout___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_withStdout___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_IO_withStdin___rarg___lambda__3___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_withStderr___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_withStderr___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_print___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_get_stdout(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_apply_2(x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_print___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_print___at_IO_println___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stdout(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_print___at_IO_println___spec__1(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_println___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_get_stderr(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_apply_2(x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprint___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stderr(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_eprint___at_IO_eprintln___spec__1(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprintln___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at_IO_eprintln___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at_IO_eprintln___spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_appDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("System.IO.appDir: unexpected filename '");
return x_1;
}
}
static lean_object* _init_l_IO_appDir___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_System_FilePath_parent(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_appDir___closed__1;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = l_IO_appDir___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_4);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_io_realpath(x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_System_FilePath_parent(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_IO_appDir___closed__1;
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_IO_appDir___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_io_realpath(x_23, x_15);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_create_dir(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_System_FilePath_isDir(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_IO_FS_createDirAll___lambda__1(x_1, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_IO_FS_createDirAll(x_7, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_FS_createDirAll___lambda__1(x_1, x_9, x_10);
lean_dec(x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = l_IO_FS_createDirAll___lambda__2(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_createDirAll___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_createDirAll___lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_createDirAll(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = l_IO_FS_DirEntry_path(x_8);
x_10 = l_System_FilePath_isDir(x_9, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_io_remove_file(x_9, x_13);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_box(0);
x_3 = x_17;
x_4 = x_18;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_IO_FS_removeDirAll(x_9, x_24);
lean_dec(x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_29 = lean_box(0);
x_3 = x_28;
x_4 = x_29;
x_5 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_read_dir(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = lean_box(0);
x_10 = l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(x_4, x_7, x_8, x_9, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_io_remove_dir(x_1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_IO_FS_removeDirAll___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_removeDirAll(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_IO_Process_Stdio_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Mode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_Process_Stdio_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_Process_Stdio_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_IO_Process_StdioConfig_stdin___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_IO_Process_StdioConfig_stdout___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_IO_Process_StdioConfig_stderr___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_IO_Process_SpawnArgs_args___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_lines___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_Process_SpawnArgs_cwd___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_IO_Process_SpawnArgs_env___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_lines___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_process_spawn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_wait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_take_stdin(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_io_error_to_string(x_3);
x_5 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
lean_ctor_set_uint8(x_4, 1, x_6);
lean_ctor_set_uint8(x_4, 2, x_6);
lean_inc(x_4);
x_7 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Task_Priority_dedicated;
x_14 = lean_io_as_task(x_12, x_13, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
x_18 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_19 = l_IO_FS_Handle_readToEnd_loop(x_17, x_18, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_io_process_child_wait(x_4, x_8, x_21);
lean_dec(x_8);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_task_get_own(x_15);
x_26 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_25, x_24);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint32_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
x_30 = lean_unbox_uint32(x_23);
lean_dec(x_23);
lean_ctor_set_uint32(x_29, sizeof(void*)*2, x_30);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_20);
x_34 = lean_unbox_uint32(x_23);
lean_dec(x_23);
lean_ctor_set_uint32(x_33, sizeof(void*)*2, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_23);
lean_dec(x_20);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_20);
lean_dec(x_15);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
x_53 = 0;
x_54 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, 2, x_53);
lean_inc(x_54);
lean_ctor_set(x_1, 0, x_54);
x_55 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___boxed), 2, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = l_Task_Priority_dedicated;
x_62 = lean_io_as_task(x_60, x_61, x_57);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_56, 2);
lean_inc(x_65);
x_66 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_67 = l_IO_FS_Handle_readToEnd_loop(x_65, x_66, x_64);
lean_dec(x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_io_process_child_wait(x_54, x_56, x_69);
lean_dec(x_56);
lean_dec(x_54);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_task_get_own(x_63);
x_74 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_73, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint32_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_68);
x_79 = lean_unbox_uint32(x_71);
lean_dec(x_71);
lean_ctor_set_uint32(x_78, sizeof(void*)*2, x_79);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_71);
lean_dec(x_68);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_83 = x_74;
} else {
 lean_dec_ref(x_74);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_68);
lean_dec(x_63);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_87 = x_70;
} else {
 lean_dec_ref(x_70);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_63);
lean_dec(x_56);
lean_dec(x_54);
x_89 = lean_ctor_get(x_67, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_67, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_91 = x_67;
} else {
 lean_dec_ref(x_67);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_54);
x_93 = lean_ctor_get(x_55, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_55, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_95 = x_55;
} else {
 lean_dec_ref(x_55);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_97 = lean_ctor_get(x_1, 0);
x_98 = lean_ctor_get(x_1, 1);
x_99 = lean_ctor_get(x_1, 2);
x_100 = lean_ctor_get(x_1, 3);
x_101 = lean_ctor_get(x_1, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_1);
x_102 = lean_ctor_get_uint8(x_97, 0);
if (lean_is_exclusive(x_97)) {
 x_103 = x_97;
} else {
 lean_dec_ref(x_97);
 x_103 = lean_box(0);
}
x_104 = 0;
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 0, 3);
} else {
 x_105 = x_103;
}
lean_ctor_set_uint8(x_105, 0, x_102);
lean_ctor_set_uint8(x_105, 1, x_104);
lean_ctor_set_uint8(x_105, 2, x_104);
lean_inc(x_105);
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_98);
lean_ctor_set(x_106, 2, x_99);
lean_ctor_set(x_106, 3, x_100);
lean_ctor_set(x_106, 4, x_101);
x_107 = lean_io_process_spawn(x_106, x_2);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
x_111 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___boxed), 2, 1);
lean_closure_set(x_111, 0, x_110);
x_112 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_112, 0, x_111);
x_113 = l_Task_Priority_dedicated;
x_114 = lean_io_as_task(x_112, x_113, x_109);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_108, 2);
lean_inc(x_117);
x_118 = l_IO_FS_instInhabitedStream___lambda__1___closed__2;
x_119 = l_IO_FS_Handle_readToEnd_loop(x_117, x_118, x_116);
lean_dec(x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_io_process_child_wait(x_105, x_108, x_121);
lean_dec(x_108);
lean_dec(x_105);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_task_get_own(x_115);
x_126 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_125, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint32_t x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_120);
x_131 = lean_unbox_uint32(x_123);
lean_dec(x_123);
lean_ctor_set_uint32(x_130, sizeof(void*)*2, x_131);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_128);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_123);
lean_dec(x_120);
x_133 = lean_ctor_get(x_126, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_126, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_135 = x_126;
} else {
 lean_dec_ref(x_126);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_120);
lean_dec(x_115);
x_137 = lean_ctor_get(x_122, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_122, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_105);
x_141 = lean_ctor_get(x_119, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_119, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_143 = x_119;
} else {
 lean_dec_ref(x_119);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_105);
x_145 = lean_ctor_get(x_107, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_107, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_147 = x_107;
} else {
 lean_dec_ref(x_107);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_IO_Process_run___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("process '");
return x_1;
}
}
static lean_object* _init_l_IO_Process_run___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' exited with code ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_IO_Process_output(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_8 = 0;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_IO_Process_run___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_IO_Process_run___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_uint32_to_nat(x_7);
x_16 = l_Nat_repr(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l_IO_Process_run___lambda__1(x_5, x_19, x_6);
lean_dec(x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get_uint32(x_21, sizeof(void*)*2);
x_24 = 0;
x_25 = lean_uint32_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_IO_Process_run___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_IO_Process_run___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_uint32_to_nat(x_23);
x_32 = l_Nat_repr(x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = l_IO_Process_run___lambda__1(x_21, x_36, x_22);
lean_dec(x_21);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
return x_3;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Process_run___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_io_exit(x_4, x_3);
return x_5;
}
}
static uint8_t _init_l_IO_AccessRight_read___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_IO_AccessRight_write___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_IO_AccessRight_execution___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__1() {
_start:
{
uint32_t x_1; uint32_t x_2; 
x_1 = 0;
x_2 = lean_uint32_lor(x_1, x_1);
return x_2;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__2() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__3() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__4() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__5() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 2;
x_3 = lean_uint32_lor(x_2, x_1);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__6() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__5;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__7() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__8() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__9() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__10() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__11() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__12() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__11;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__13() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = lean_uint32_lor(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, 0);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, 2);
if (x_4 == 0)
{
uint32_t x_5; 
x_5 = l_IO_AccessRight_flags___closed__2;
return x_5;
}
else
{
uint32_t x_6; 
x_6 = l_IO_AccessRight_flags___closed__4;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, 2);
if (x_7 == 0)
{
uint32_t x_8; 
x_8 = l_IO_AccessRight_flags___closed__6;
return x_8;
}
else
{
uint32_t x_9; 
x_9 = l_IO_AccessRight_flags___closed__8;
return x_9;
}
}
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, 1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, 2);
if (x_11 == 0)
{
uint32_t x_12; 
x_12 = l_IO_AccessRight_flags___closed__9;
return x_12;
}
else
{
uint32_t x_13; 
x_13 = l_IO_AccessRight_flags___closed__10;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, 2);
if (x_14 == 0)
{
uint32_t x_15; 
x_15 = l_IO_AccessRight_flags___closed__12;
return x_15;
}
else
{
uint32_t x_16; 
x_16 = l_IO_AccessRight_flags___closed__13;
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_AccessRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FileRight_user___default___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FileRight_user___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FileRight_user___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FileRight_group___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FileRight_user___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_IO_FileRight_other___default() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FileRight_user___default___closed__1;
return x_1;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; uint32_t x_7; uint32_t x_8; uint32_t x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_IO_AccessRight_flags(x_2);
x_4 = 6;
x_5 = lean_uint32_shift_left(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_IO_AccessRight_flags(x_6);
x_8 = 3;
x_9 = lean_uint32_shift_left(x_7, x_8);
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_IO_AccessRight_flags(x_10);
x_12 = lean_uint32_lor(x_9, x_11);
x_13 = lean_uint32_lor(x_5, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_FileRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_IO_FileRight_flags(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_setAccessRights(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_read(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__6___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__5___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__4___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__3___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__1___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofHandle___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofHandle___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofHandle___elambda__4(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofHandle___elambda__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_Buffer_data___default() {
_start:
{
lean_object* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_Buffer_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_string_to_utf8(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_byte_array_size(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
lean_inc(x_10);
lean_inc(x_9);
x_13 = lean_byte_array_copy_slice(x_7, x_11, x_8, x_9, x_10, x_12);
lean_dec(x_7);
x_14 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_st_ref_set(x_1, x_15, x_6);
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
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_byte_array_get(x_1, x_2);
x_7 = 0;
x_8 = lean_uint8_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = 10;
x_10 = lean_uint8_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_byte_array_size(x_7);
x_11 = l_ByteArray_extract(x_7, x_8, x_10);
x_12 = lean_string_from_utf8_unchecked(x_11);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_10);
x_13 = lean_st_ref_set(x_1, x_4, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_byte_array_get(x_7, x_18);
x_20 = 0;
x_21 = lean_uint8_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_18, x_22);
lean_dec(x_18);
x_24 = l_ByteArray_extract(x_7, x_8, x_23);
x_25 = lean_string_from_utf8_unchecked(x_24);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_23);
x_26 = lean_st_ref_set(x_1, x_4, x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_ByteArray_extract(x_7, x_8, x_18);
x_32 = lean_string_from_utf8_unchecked(x_31);
lean_dec(x_31);
lean_ctor_set(x_4, 1, x_18);
x_33 = lean_st_ref_set(x_1, x_4, x_5);
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
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
lean_inc(x_39);
x_40 = l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_byte_array_size(x_38);
x_42 = l_ByteArray_extract(x_38, x_39, x_41);
x_43 = lean_string_from_utf8_unchecked(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_st_ref_set(x_1, x_44, x_5);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_byte_array_get(x_38, x_49);
x_51 = 0;
x_52 = lean_uint8_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_49, x_53);
lean_dec(x_49);
x_55 = l_ByteArray_extract(x_38, x_39, x_54);
x_56 = lean_string_from_utf8_unchecked(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_st_ref_set(x_1, x_57, x_5);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = l_ByteArray_extract(x_38, x_39, x_49);
x_63 = lean_string_from_utf8_unchecked(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_38);
lean_ctor_set(x_64, 1, x_49);
x_65 = lean_st_ref_set(x_1, x_64, x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_byte_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
x_12 = lean_byte_array_copy_slice(x_2, x_10, x_7, x_8, x_9, x_11);
x_13 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_st_ref_set(x_1, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_usize_to_nat(x_2);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_inc(x_9);
x_12 = l_ByteArray_extract(x_8, x_9, x_11);
lean_dec(x_11);
x_13 = lean_byte_array_size(x_12);
x_14 = lean_nat_add(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_14);
x_15 = lean_st_ref_set(x_1, x_5, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_usize_to_nat(x_2);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_inc(x_21);
x_24 = l_ByteArray_extract(x_20, x_21, x_23);
lean_dec(x_23);
x_25 = lean_byte_array_size(x_24);
x_26 = lean_nat_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_st_ref_set(x_1, x_27, x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_nat_dec_le(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_box(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_byte_array_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_IO_FS_Stream_ofBuffer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__5), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__6), 2, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__4___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__3___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__1___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_IO_FS_Stream_ofBuffer___closed__1;
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set(x_9, 5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_findIdx_x3f_loop___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___elambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofBuffer___elambda__4(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_string_from_utf8_unchecked(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_IO_FS_Stream_ofBuffer(x_1);
lean_inc(x_7);
x_9 = l_IO_FS_Stream_ofBuffer(x_7);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_withStderr___rarg(x_2, x_3, x_4, x_9, x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_IO_withStdout___rarg(x_2, x_3, x_4, x_9, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l_IO_withStdin___rarg(x_2, x_3, x_4, x_8, x_11);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__2), 5, 4);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_6);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__3), 7, 6);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_withIsolatedStreams___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_IO_FS_withIsolatedStreams___rarg___closed__2;
lean_inc(x_3);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
lean_inc(x_7);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__4), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
lean_closure_set(x_8, 5, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_withIsolatedStreams___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_IO_println___spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = l_IO_println___at_Lean_instEval___spec__1(x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEval___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEval___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_Lean_instEval__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Std_Format_defWidth;
x_4 = lean_format_pretty(x_1, x_3);
x_5 = 10;
x_6 = lean_string_push(x_4, x_5);
x_7 = l_IO_print___at_IO_println___spec__1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = l_IO_println___at_Lean_instEval__1___spec__1(x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEval__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEval__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEval__1___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_instEvalUnit___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("()");
return x_1;
}
}
static lean_object* _init_l_Lean_instEvalUnit___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instEvalUnit___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instEvalUnit___rarg___closed__2;
x_4 = l_IO_println___at_Lean_instEval__1___spec__1(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEvalUnit___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_instEvalUnit___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalUnit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instEvalUnit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_2(x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_apply_3(x_1, x_9, x_11, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instEvalIO___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEvalIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_instEvalIO___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_runEval___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stderr(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stderr(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stderr(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_runEval___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdout(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdout(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdout(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_runEval___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdin(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdin(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdin(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_IO_FS_withIsolatedStreams___rarg___closed__1;
x_4 = lean_st_mk_ref(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_mk_ref(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_IO_FS_Stream_ofBuffer(x_5);
lean_inc(x_8);
x_11 = l_IO_FS_Stream_ofBuffer(x_8);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lean_runEval___spec__2), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_runEval___spec__3), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_IO_withStdin___at_Lean_runEval___spec__4(x_10, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_string_from_utf8_unchecked(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_string_from_utf8_unchecked(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_runEval___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box(x_4);
x_6 = lean_apply_3(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_runEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_runEval___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_IO_FS_withIsolatedStreams___at_Lean_runEval___spec__1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_runEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_runEval___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termPrintln!__");
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("andthen");
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("println! ");
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_termPrintln_x21_______closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orelse");
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("interpolatedStr");
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_termPrintln_x21_______closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_termPrintln_x21_______closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_termPrintln_x21_______closed__10;
x_2 = l_termPrintln_x21_______closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__8;
x_2 = l_termPrintln_x21_______closed__14;
x_3 = l_termPrintln_x21_______closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__4;
x_2 = l_termPrintln_x21_______closed__6;
x_3 = l_termPrintln_x21_______closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21_______closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_termPrintln_x21_______closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_termPrintln_x21_______closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_termPrintln_x21____() {
_start:
{
lean_object* x_1; 
x_1 = l_termPrintln_x21_______closed__17;
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO.println");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("println");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeAscription");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6;
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unit");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termS!_");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("s!");
return x_1;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_3 = l_IO_FS_lines___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_termPrintln_x21_______closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l_Lean_interpolatedStrKind;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_2);
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
lean_inc(x_16);
lean_inc(x_17);
x_21 = l_Lean_addMacroScope(x_17, x_20, x_16);
x_22 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_23 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
lean_inc(x_15);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
x_26 = lean_array_push(x_25, x_9);
x_27 = lean_box(2);
x_28 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
x_30 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_31 = lean_array_push(x_30, x_24);
x_32 = lean_array_push(x_31, x_29);
x_33 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
x_35 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
lean_inc(x_15);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_inc(x_16);
lean_inc(x_17);
x_38 = l_Lean_addMacroScope(x_17, x_37, x_16);
x_39 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
x_40 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
lean_inc(x_15);
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
x_42 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
x_43 = l_Lean_addMacroScope(x_17, x_42, x_16);
x_44 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
x_45 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
lean_inc(x_15);
x_46 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_array_push(x_25, x_46);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_27);
lean_ctor_set(x_48, 1, x_28);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_array_push(x_30, x_41);
x_50 = lean_array_push(x_49, x_48);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_33);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_array_push(x_30, x_36);
x_53 = lean_array_push(x_52, x_51);
x_54 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
x_56 = lean_array_push(x_25, x_55);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_27);
lean_ctor_set(x_57, 1, x_28);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_array_push(x_30, x_34);
x_59 = lean_array_push(x_58, x_57);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_28);
lean_ctor_set(x_60, 2, x_59);
x_61 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_15);
lean_ctor_set(x_62, 1, x_61);
x_63 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
x_64 = lean_array_push(x_63, x_19);
x_65 = lean_array_push(x_64, x_60);
x_66 = lean_array_push(x_65, x_62);
x_67 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_27);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_66);
lean_ctor_set(x_13, 0, x_68);
return x_13;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_69 = lean_ctor_get(x_13, 0);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_13);
x_71 = lean_ctor_get(x_2, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_69);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
lean_inc(x_71);
lean_inc(x_72);
x_76 = l_Lean_addMacroScope(x_72, x_75, x_71);
x_77 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_78 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
lean_inc(x_69);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_78);
x_80 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
x_81 = lean_array_push(x_80, x_9);
x_82 = lean_box(2);
x_83 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_81);
x_85 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_86 = lean_array_push(x_85, x_79);
x_87 = lean_array_push(x_86, x_84);
x_88 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_87);
x_90 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
lean_inc(x_69);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_69);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_inc(x_71);
lean_inc(x_72);
x_93 = l_Lean_addMacroScope(x_72, x_92, x_71);
x_94 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
x_95 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
lean_inc(x_69);
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_69);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_95);
x_97 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
x_98 = l_Lean_addMacroScope(x_72, x_97, x_71);
x_99 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
x_100 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
lean_inc(x_69);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_69);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
x_102 = lean_array_push(x_80, x_101);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_82);
lean_ctor_set(x_103, 1, x_83);
lean_ctor_set(x_103, 2, x_102);
x_104 = lean_array_push(x_85, x_96);
x_105 = lean_array_push(x_104, x_103);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_82);
lean_ctor_set(x_106, 1, x_88);
lean_ctor_set(x_106, 2, x_105);
x_107 = lean_array_push(x_85, x_91);
x_108 = lean_array_push(x_107, x_106);
x_109 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_82);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
x_111 = lean_array_push(x_80, x_110);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_82);
lean_ctor_set(x_112, 1, x_83);
lean_ctor_set(x_112, 2, x_111);
x_113 = lean_array_push(x_85, x_89);
x_114 = lean_array_push(x_113, x_112);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_82);
lean_ctor_set(x_115, 1, x_83);
lean_ctor_set(x_115, 2, x_114);
x_116 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_69);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
x_119 = lean_array_push(x_118, x_74);
x_120 = lean_array_push(x_119, x_115);
x_121 = lean_array_push(x_120, x_117);
x_122 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_82);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_70);
return x_124;
}
}
else
{
lean_object* x_125; uint8_t x_126; 
lean_inc(x_2);
x_125 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_3);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_2, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
lean_dec(x_2);
x_130 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_127);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
lean_inc(x_128);
lean_inc(x_129);
x_133 = l_Lean_addMacroScope(x_129, x_132, x_128);
x_134 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_135 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
lean_inc(x_127);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_135);
x_137 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42;
lean_inc(x_127);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_137);
x_139 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_140 = lean_array_push(x_139, x_138);
x_141 = lean_array_push(x_140, x_9);
x_142 = lean_box(2);
x_143 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41;
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_141);
x_145 = lean_array_push(x_139, x_144);
x_146 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43;
x_147 = lean_array_push(x_145, x_146);
x_148 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_142);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_147);
x_150 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
lean_inc(x_127);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_127);
lean_ctor_set(x_151, 1, x_150);
x_152 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
x_153 = lean_array_push(x_152, x_131);
lean_inc(x_153);
x_154 = lean_array_push(x_153, x_149);
lean_inc(x_151);
x_155 = lean_array_push(x_154, x_151);
x_156 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_142);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_155);
x_158 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
x_159 = lean_array_push(x_158, x_157);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_142);
lean_ctor_set(x_160, 1, x_148);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_array_push(x_139, x_136);
x_162 = lean_array_push(x_161, x_160);
x_163 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_162);
x_165 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
lean_inc(x_127);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_127);
lean_ctor_set(x_166, 1, x_165);
x_167 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_inc(x_128);
lean_inc(x_129);
x_168 = l_Lean_addMacroScope(x_129, x_167, x_128);
x_169 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
x_170 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
lean_inc(x_127);
x_171 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_171, 0, x_127);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_170);
x_172 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
x_173 = l_Lean_addMacroScope(x_129, x_172, x_128);
x_174 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
x_175 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
x_176 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_176, 0, x_127);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_173);
lean_ctor_set(x_176, 3, x_175);
x_177 = lean_array_push(x_158, x_176);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_142);
lean_ctor_set(x_178, 1, x_148);
lean_ctor_set(x_178, 2, x_177);
x_179 = lean_array_push(x_139, x_171);
x_180 = lean_array_push(x_179, x_178);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_142);
lean_ctor_set(x_181, 1, x_163);
lean_ctor_set(x_181, 2, x_180);
x_182 = lean_array_push(x_139, x_166);
x_183 = lean_array_push(x_182, x_181);
x_184 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
x_185 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_185, 0, x_142);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_183);
x_186 = lean_array_push(x_158, x_185);
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_142);
lean_ctor_set(x_187, 1, x_148);
lean_ctor_set(x_187, 2, x_186);
x_188 = lean_array_push(x_139, x_164);
x_189 = lean_array_push(x_188, x_187);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_142);
lean_ctor_set(x_190, 1, x_148);
lean_ctor_set(x_190, 2, x_189);
x_191 = lean_array_push(x_153, x_190);
x_192 = lean_array_push(x_191, x_151);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_142);
lean_ctor_set(x_193, 1, x_156);
lean_ctor_set(x_193, 2, x_192);
lean_ctor_set(x_125, 0, x_193);
return x_125;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_194 = lean_ctor_get(x_125, 0);
x_195 = lean_ctor_get(x_125, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_125);
x_196 = lean_ctor_get(x_2, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_2, 1);
lean_inc(x_197);
lean_dec(x_2);
x_198 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
lean_inc(x_194);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_198);
x_200 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20;
lean_inc(x_196);
lean_inc(x_197);
x_201 = l_Lean_addMacroScope(x_197, x_200, x_196);
x_202 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16;
x_203 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22;
lean_inc(x_194);
x_204 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_204, 0, x_194);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_201);
lean_ctor_set(x_204, 3, x_203);
x_205 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42;
lean_inc(x_194);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_194);
lean_ctor_set(x_206, 1, x_205);
x_207 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
x_208 = lean_array_push(x_207, x_206);
x_209 = lean_array_push(x_208, x_9);
x_210 = lean_box(2);
x_211 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41;
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_209);
x_213 = lean_array_push(x_207, x_212);
x_214 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43;
x_215 = lean_array_push(x_213, x_214);
x_216 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11;
x_217 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_217, 2, x_215);
x_218 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38;
lean_inc(x_194);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_194);
lean_ctor_set(x_219, 1, x_218);
x_220 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39;
x_221 = lean_array_push(x_220, x_199);
lean_inc(x_221);
x_222 = lean_array_push(x_221, x_217);
lean_inc(x_219);
x_223 = lean_array_push(x_222, x_219);
x_224 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8;
x_225 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_225, 0, x_210);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_223);
x_226 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23;
x_227 = lean_array_push(x_226, x_225);
x_228 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_228, 0, x_210);
lean_ctor_set(x_228, 1, x_216);
lean_ctor_set(x_228, 2, x_227);
x_229 = lean_array_push(x_207, x_204);
x_230 = lean_array_push(x_229, x_228);
x_231 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13;
x_232 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_232, 0, x_210);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_230);
x_233 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27;
lean_inc(x_194);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_194);
lean_ctor_set(x_234, 1, x_233);
x_235 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18;
lean_inc(x_196);
lean_inc(x_197);
x_236 = l_Lean_addMacroScope(x_197, x_235, x_196);
x_237 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29;
x_238 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
lean_inc(x_194);
x_239 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_239, 0, x_194);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_236);
lean_ctor_set(x_239, 3, x_238);
x_240 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35;
x_241 = l_Lean_addMacroScope(x_197, x_240, x_196);
x_242 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34;
x_243 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37;
x_244 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_244, 0, x_194);
lean_ctor_set(x_244, 1, x_242);
lean_ctor_set(x_244, 2, x_241);
lean_ctor_set(x_244, 3, x_243);
x_245 = lean_array_push(x_226, x_244);
x_246 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_246, 0, x_210);
lean_ctor_set(x_246, 1, x_216);
lean_ctor_set(x_246, 2, x_245);
x_247 = lean_array_push(x_207, x_239);
x_248 = lean_array_push(x_247, x_246);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_210);
lean_ctor_set(x_249, 1, x_231);
lean_ctor_set(x_249, 2, x_248);
x_250 = lean_array_push(x_207, x_234);
x_251 = lean_array_push(x_250, x_249);
x_252 = l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26;
x_253 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_253, 0, x_210);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_251);
x_254 = lean_array_push(x_226, x_253);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_210);
lean_ctor_set(x_255, 1, x_216);
lean_ctor_set(x_255, 2, x_254);
x_256 = lean_array_push(x_207, x_232);
x_257 = lean_array_push(x_256, x_255);
x_258 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_258, 0, x_210);
lean_ctor_set(x_258, 1, x_216);
lean_ctor_set(x_258, 2, x_257);
x_259 = lean_array_push(x_221, x_258);
x_260 = lean_array_push(x_259, x_219);
x_261 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_261, 0, x_210);
lean_ctor_set(x_261, 1, x_224);
lean_ctor_set(x_261, 2, x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_195);
return x_262;
}
}
}
}
}
lean_object* initialize_Init_Control_EState(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Reader(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IOError(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_ST(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_EState(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instMonadEIO___closed__1 = _init_l_instMonadEIO___closed__1();
lean_mark_persistent(l_instMonadEIO___closed__1);
l_instMonadFinallyEIO___closed__1 = _init_l_instMonadFinallyEIO___closed__1();
lean_mark_persistent(l_instMonadFinallyEIO___closed__1);
l_instMonadExceptOfEIO___closed__1 = _init_l_instMonadExceptOfEIO___closed__1();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__1);
l_instMonadExceptOfEIO___closed__2 = _init_l_instMonadExceptOfEIO___closed__2();
lean_mark_persistent(l_instMonadExceptOfEIO___closed__2);
l_instMonadBaseIO = _init_l_instMonadBaseIO();
lean_mark_persistent(l_instMonadBaseIO);
l_instMonadFinallyBaseIO = _init_l_instMonadFinallyBaseIO();
lean_mark_persistent(l_instMonadFinallyBaseIO);
l_IO_FS_Mode_noConfusion___rarg___closed__1 = _init_l_IO_FS_Mode_noConfusion___rarg___closed__1();
lean_mark_persistent(l_IO_FS_Mode_noConfusion___rarg___closed__1);
l_IO_FS_instInhabitedStream___lambda__1___closed__1 = _init_l_IO_FS_instInhabitedStream___lambda__1___closed__1();
l_IO_FS_instInhabitedStream___lambda__1___closed__2 = _init_l_IO_FS_instInhabitedStream___lambda__1___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedStream___lambda__1___closed__2);
l_IO_FS_instInhabitedStream___lambda__1___closed__3 = _init_l_IO_FS_instInhabitedStream___lambda__1___closed__3();
lean_mark_persistent(l_IO_FS_instInhabitedStream___lambda__1___closed__3);
l_IO_FS_instInhabitedStream___closed__1 = _init_l_IO_FS_instInhabitedStream___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__1);
l_IO_FS_instInhabitedStream___closed__2 = _init_l_IO_FS_instInhabitedStream___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__2);
l_IO_FS_instInhabitedStream___closed__3 = _init_l_IO_FS_instInhabitedStream___closed__3();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__3);
l_IO_FS_instInhabitedStream___closed__4 = _init_l_IO_FS_instInhabitedStream___closed__4();
lean_mark_persistent(l_IO_FS_instInhabitedStream___closed__4);
l_IO_FS_instInhabitedStream = _init_l_IO_FS_instInhabitedStream();
lean_mark_persistent(l_IO_FS_instInhabitedStream);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__1);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__2);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__3 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__3);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__4);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__5 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__5);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__6);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__7 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__7);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__8 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__8);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__9);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__10 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__10);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__11 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__11();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__11);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__12);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__13 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__13();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__13);
l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__14 = _init_l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__14();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_Handle_fopenFlags___closed__14);
l_IO_FS_lines___closed__1 = _init_l_IO_FS_lines___closed__1();
lean_mark_persistent(l_IO_FS_lines___closed__1);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__1);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__2);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__3);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__4);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__5);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__6);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__7);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__8 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__8);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__9 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__9);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__10);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__11 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__11();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__11);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__12 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__12();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__12);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__13);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__14 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__14();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__14);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__15);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__16);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__17 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__17();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__17);
l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18 = _init_l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprDirEntry____x40_Init_System_IO___hyg_1891____closed__18);
l_IO_FS_instReprDirEntry___closed__1 = _init_l_IO_FS_instReprDirEntry___closed__1();
lean_mark_persistent(l_IO_FS_instReprDirEntry___closed__1);
l_IO_FS_instReprDirEntry = _init_l_IO_FS_instReprDirEntry();
lean_mark_persistent(l_IO_FS_instReprDirEntry);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__1);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__2);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__3);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__4);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__5);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__6);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__7);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__8 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__8);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__9 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__9);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__10);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__11 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__11();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__11);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__12 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__12();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__12);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__13 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__13();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__13);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__14 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__14();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__14);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__15 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__15();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__15);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__16);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__17 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__17();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__17);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__18 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__18();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__18);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__19 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__19();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__19);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__20 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__20();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__20);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__21 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__21();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__21);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__22);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__23 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__23();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__23);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__24 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__24();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__24);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__25 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__25();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__25);
l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__26 = _init_l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__26();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprFileType____x40_Init_System_IO___hyg_1946____closed__26);
l_IO_FS_instReprFileType___closed__1 = _init_l_IO_FS_instReprFileType___closed__1();
lean_mark_persistent(l_IO_FS_instReprFileType___closed__1);
l_IO_FS_instReprFileType = _init_l_IO_FS_instReprFileType();
lean_mark_persistent(l_IO_FS_instReprFileType);
l_IO_FS_instBEqFileType___closed__1 = _init_l_IO_FS_instBEqFileType___closed__1();
lean_mark_persistent(l_IO_FS_instBEqFileType___closed__1);
l_IO_FS_instBEqFileType = _init_l_IO_FS_instBEqFileType();
lean_mark_persistent(l_IO_FS_instBEqFileType);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__1);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__2);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__3);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__4);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__5);
l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprSystemTime____x40_Init_System_IO___hyg_2122____closed__6);
l_IO_FS_instReprSystemTime___closed__1 = _init_l_IO_FS_instReprSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instReprSystemTime___closed__1);
l_IO_FS_instReprSystemTime = _init_l_IO_FS_instReprSystemTime();
lean_mark_persistent(l_IO_FS_instReprSystemTime);
l_IO_FS_instBEqSystemTime___closed__1 = _init_l_IO_FS_instBEqSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instBEqSystemTime___closed__1);
l_IO_FS_instBEqSystemTime = _init_l_IO_FS_instBEqSystemTime();
lean_mark_persistent(l_IO_FS_instBEqSystemTime);
l_IO_FS_instOrdSystemTime___closed__1 = _init_l_IO_FS_instOrdSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instOrdSystemTime___closed__1);
l_IO_FS_instOrdSystemTime = _init_l_IO_FS_instOrdSystemTime();
lean_mark_persistent(l_IO_FS_instOrdSystemTime);
l_IO_FS_instInhabitedSystemTime___closed__1 = _init_l_IO_FS_instInhabitedSystemTime___closed__1();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime___closed__1);
l_IO_FS_instInhabitedSystemTime___closed__2 = _init_l_IO_FS_instInhabitedSystemTime___closed__2();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime___closed__2);
l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
lean_mark_persistent(l_IO_FS_instLTSystemTime);
l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
lean_mark_persistent(l_IO_FS_instLESystemTime);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__1 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__1();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__1);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__2 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__2();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__2);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__3 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__3();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__3);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__4 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__4();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__4);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__5 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__5();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__5);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__6 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__6();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__6);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__7 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__7();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__7);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__8 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__8();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__8);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__9 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__9();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__9);
l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__10 = _init_l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__10();
lean_mark_persistent(l___private_Init_System_IO_0__IO_FS_reprMetadata____x40_Init_System_IO___hyg_2361____closed__10);
l_IO_FS_instReprMetadata___closed__1 = _init_l_IO_FS_instReprMetadata___closed__1();
lean_mark_persistent(l_IO_FS_instReprMetadata___closed__1);
l_IO_FS_instReprMetadata = _init_l_IO_FS_instReprMetadata();
lean_mark_persistent(l_IO_FS_instReprMetadata);
l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_System_FilePath_walkDir_go___spec__1___closed__1);
l_IO_withStdin___rarg___lambda__3___closed__1 = _init_l_IO_withStdin___rarg___lambda__3___closed__1();
lean_mark_persistent(l_IO_withStdin___rarg___lambda__3___closed__1);
l_IO_appDir___closed__1 = _init_l_IO_appDir___closed__1();
lean_mark_persistent(l_IO_appDir___closed__1);
l_IO_appDir___closed__2 = _init_l_IO_appDir___closed__2();
lean_mark_persistent(l_IO_appDir___closed__2);
l_IO_Process_StdioConfig_stdin___default = _init_l_IO_Process_StdioConfig_stdin___default();
l_IO_Process_StdioConfig_stdout___default = _init_l_IO_Process_StdioConfig_stdout___default();
l_IO_Process_StdioConfig_stderr___default = _init_l_IO_Process_StdioConfig_stderr___default();
l_IO_Process_SpawnArgs_args___default = _init_l_IO_Process_SpawnArgs_args___default();
lean_mark_persistent(l_IO_Process_SpawnArgs_args___default);
l_IO_Process_SpawnArgs_cwd___default = _init_l_IO_Process_SpawnArgs_cwd___default();
lean_mark_persistent(l_IO_Process_SpawnArgs_cwd___default);
l_IO_Process_SpawnArgs_env___default = _init_l_IO_Process_SpawnArgs_env___default();
lean_mark_persistent(l_IO_Process_SpawnArgs_env___default);
l_IO_Process_run___closed__1 = _init_l_IO_Process_run___closed__1();
lean_mark_persistent(l_IO_Process_run___closed__1);
l_IO_Process_run___closed__2 = _init_l_IO_Process_run___closed__2();
lean_mark_persistent(l_IO_Process_run___closed__2);
l_IO_AccessRight_read___default = _init_l_IO_AccessRight_read___default();
l_IO_AccessRight_write___default = _init_l_IO_AccessRight_write___default();
l_IO_AccessRight_execution___default = _init_l_IO_AccessRight_execution___default();
l_IO_AccessRight_flags___closed__1 = _init_l_IO_AccessRight_flags___closed__1();
l_IO_AccessRight_flags___closed__2 = _init_l_IO_AccessRight_flags___closed__2();
l_IO_AccessRight_flags___closed__3 = _init_l_IO_AccessRight_flags___closed__3();
l_IO_AccessRight_flags___closed__4 = _init_l_IO_AccessRight_flags___closed__4();
l_IO_AccessRight_flags___closed__5 = _init_l_IO_AccessRight_flags___closed__5();
l_IO_AccessRight_flags___closed__6 = _init_l_IO_AccessRight_flags___closed__6();
l_IO_AccessRight_flags___closed__7 = _init_l_IO_AccessRight_flags___closed__7();
l_IO_AccessRight_flags___closed__8 = _init_l_IO_AccessRight_flags___closed__8();
l_IO_AccessRight_flags___closed__9 = _init_l_IO_AccessRight_flags___closed__9();
l_IO_AccessRight_flags___closed__10 = _init_l_IO_AccessRight_flags___closed__10();
l_IO_AccessRight_flags___closed__11 = _init_l_IO_AccessRight_flags___closed__11();
l_IO_AccessRight_flags___closed__12 = _init_l_IO_AccessRight_flags___closed__12();
l_IO_AccessRight_flags___closed__13 = _init_l_IO_AccessRight_flags___closed__13();
l_IO_FileRight_user___default___closed__1 = _init_l_IO_FileRight_user___default___closed__1();
lean_mark_persistent(l_IO_FileRight_user___default___closed__1);
l_IO_FileRight_user___default = _init_l_IO_FileRight_user___default();
lean_mark_persistent(l_IO_FileRight_user___default);
l_IO_FileRight_group___default = _init_l_IO_FileRight_group___default();
lean_mark_persistent(l_IO_FileRight_group___default);
l_IO_FileRight_other___default = _init_l_IO_FileRight_other___default();
lean_mark_persistent(l_IO_FileRight_other___default);
l_IO_FS_Stream_Buffer_data___default = _init_l_IO_FS_Stream_Buffer_data___default();
lean_mark_persistent(l_IO_FS_Stream_Buffer_data___default);
l_IO_FS_Stream_Buffer_pos___default = _init_l_IO_FS_Stream_Buffer_pos___default();
lean_mark_persistent(l_IO_FS_Stream_Buffer_pos___default);
l_IO_FS_Stream_ofBuffer___closed__1 = _init_l_IO_FS_Stream_ofBuffer___closed__1();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___closed__1);
l_IO_FS_withIsolatedStreams___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__1);
l_IO_FS_withIsolatedStreams___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__2);
l_Lean_instEvalUnit___rarg___closed__1 = _init_l_Lean_instEvalUnit___rarg___closed__1();
lean_mark_persistent(l_Lean_instEvalUnit___rarg___closed__1);
l_Lean_instEvalUnit___rarg___closed__2 = _init_l_Lean_instEvalUnit___rarg___closed__2();
lean_mark_persistent(l_Lean_instEvalUnit___rarg___closed__2);
l_termPrintln_x21_______closed__1 = _init_l_termPrintln_x21_______closed__1();
lean_mark_persistent(l_termPrintln_x21_______closed__1);
l_termPrintln_x21_______closed__2 = _init_l_termPrintln_x21_______closed__2();
lean_mark_persistent(l_termPrintln_x21_______closed__2);
l_termPrintln_x21_______closed__3 = _init_l_termPrintln_x21_______closed__3();
lean_mark_persistent(l_termPrintln_x21_______closed__3);
l_termPrintln_x21_______closed__4 = _init_l_termPrintln_x21_______closed__4();
lean_mark_persistent(l_termPrintln_x21_______closed__4);
l_termPrintln_x21_______closed__5 = _init_l_termPrintln_x21_______closed__5();
lean_mark_persistent(l_termPrintln_x21_______closed__5);
l_termPrintln_x21_______closed__6 = _init_l_termPrintln_x21_______closed__6();
lean_mark_persistent(l_termPrintln_x21_______closed__6);
l_termPrintln_x21_______closed__7 = _init_l_termPrintln_x21_______closed__7();
lean_mark_persistent(l_termPrintln_x21_______closed__7);
l_termPrintln_x21_______closed__8 = _init_l_termPrintln_x21_______closed__8();
lean_mark_persistent(l_termPrintln_x21_______closed__8);
l_termPrintln_x21_______closed__9 = _init_l_termPrintln_x21_______closed__9();
lean_mark_persistent(l_termPrintln_x21_______closed__9);
l_termPrintln_x21_______closed__10 = _init_l_termPrintln_x21_______closed__10();
lean_mark_persistent(l_termPrintln_x21_______closed__10);
l_termPrintln_x21_______closed__11 = _init_l_termPrintln_x21_______closed__11();
lean_mark_persistent(l_termPrintln_x21_______closed__11);
l_termPrintln_x21_______closed__12 = _init_l_termPrintln_x21_______closed__12();
lean_mark_persistent(l_termPrintln_x21_______closed__12);
l_termPrintln_x21_______closed__13 = _init_l_termPrintln_x21_______closed__13();
lean_mark_persistent(l_termPrintln_x21_______closed__13);
l_termPrintln_x21_______closed__14 = _init_l_termPrintln_x21_______closed__14();
lean_mark_persistent(l_termPrintln_x21_______closed__14);
l_termPrintln_x21_______closed__15 = _init_l_termPrintln_x21_______closed__15();
lean_mark_persistent(l_termPrintln_x21_______closed__15);
l_termPrintln_x21_______closed__16 = _init_l_termPrintln_x21_______closed__16();
lean_mark_persistent(l_termPrintln_x21_______closed__16);
l_termPrintln_x21_______closed__17 = _init_l_termPrintln_x21_______closed__17();
lean_mark_persistent(l_termPrintln_x21_______closed__17);
l_termPrintln_x21____ = _init_l_termPrintln_x21____();
lean_mark_persistent(l_termPrintln_x21____);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42);
l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43 = _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43();
lean_mark_persistent(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__43);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
