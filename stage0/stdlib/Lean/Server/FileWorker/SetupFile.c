// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: public import Lean.Server.Utils public import Lean.Util.LakePath public import Lean.Server.ServerTask
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
static const lean_string_object l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value;
lean_object* lean_io_prim_handle_get_line(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value;
static const lean_ctor_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setup-file"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--no-build"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--no-cache"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value;
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_load_dynlib(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Invalid output from `"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__5_value;
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_Lean_determineLakePath();
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_io_prim_handle_get_line(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_27; 
x_7 = lean_ctor_get(x_6, 0);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
x_8 = x_6;
x_9 = x_27;
goto block_26;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_del_object(x_8);
lean_inc_ref(x_1);
lean_inc(x_7);
x_12 = lean_apply_2(x_1, x_7, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = lean_string_append(x_3, x_7);
lean_dec(x_7);
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_16 = x_12;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec_ref(x_1);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_3);
x_23 = x_8;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
x_4 = x_1;
x_5 = x_12;
goto block_11;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_mk_io_user_error(x_6);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_7);
x_8 = x_4;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_14 = x_1;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3));
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_111 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4));
x_112 = lean_obj_once(&l_Lean_Server_FileWorker_runLakeSetupFile___closed__5, &l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once, _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
x_113 = lean_array_push(x_112, x_3);
x_114 = lean_array_push(x_113, x_111);
if (x_110 == 2)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6));
x_116 = lean_array_push(x_114, x_115);
x_117 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7));
x_118 = lean_array_push(x_116, x_117);
x_7 = x_118;
goto block_109;
}
else
{
x_7 = x_114;
goto block_109;
}
block_109:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0));
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1));
x_12 = 1;
x_13 = 0;
lean_inc_ref(x_7);
lean_inc_ref(x_2);
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_9);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
lean_inc_ref(x_14);
x_15 = lean_io_process_spawn(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_io_process_child_take_stdin(x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_instToJsonModuleHeader_toJson(x_4);
x_22 = l_Lean_Json_compress(x_21);
x_23 = l_IO_FS_Handle_putStrLn(x_19, x_22);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_23);
x_24 = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
lean_inc(x_20);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_7);
lean_closure_set(x_25, 3, x_20);
lean_closure_set(x_25, 4, x_24);
x_26 = l_Lean_Server_ServerTask_IO_asTask___redArg(x_25);
x_27 = lean_ctor_get(x_20, 1);
x_28 = l_IO_FS_Handle_readToEnd(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_task_get_own(x_26);
x_31 = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_65; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2));
x_34 = lean_io_process_child_wait(x_33, x_20);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_20, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_20, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_20, 0);
lean_dec(x_68);
x_35 = x_20;
x_36 = x_65;
goto block_64;
}
else
{
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = x_65;
goto block_64;
}
block_64:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_55; 
x_37 = lean_ctor_get(x_34, 0);
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
x_38 = x_34;
x_39 = x_55;
goto block_54;
}
else
{
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_string_utf8_byte_size(x_29);
if (x_36 == 0)
{
lean_ctor_set(x_35, 2, x_40);
lean_ctor_set(x_35, 1, x_10);
lean_ctor_set(x_35, 0, x_29);
x_41 = x_35;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_29);
lean_ctor_set(x_53, 1, x_10);
lean_ctor_set(x_53, 2, x_40);
x_41 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; lean_object* x_49; 
x_42 = l_String_Slice_trimAscii(x_41);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
lean_dec_ref(x_42);
x_46 = lean_string_utf8_extract(x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
x_47 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_32);
x_48 = lean_unbox_uint32(x_37);
lean_dec(x_37);
lean_ctor_set_uint32(x_47, sizeof(void*)*3, x_48);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_47);
x_49 = x_38;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_47);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_del_object(x_35);
lean_dec(x_32);
lean_dec(x_29);
lean_dec_ref(x_14);
x_56 = lean_ctor_get(x_34, 0);
x_63 = !lean_is_exclusive(x_34);
if (x_63 == 0)
{
x_57 = x_34;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_34);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec_ref(x_14);
x_69 = lean_ctor_get(x_31, 0);
x_76 = !lean_is_exclusive(x_31);
if (x_76 == 0)
{
x_70 = x_31;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_dec(x_31);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_69);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec_ref(x_26);
lean_dec(x_20);
lean_dec_ref(x_14);
x_77 = lean_ctor_get(x_28, 0);
x_84 = !lean_is_exclusive(x_28);
if (x_84 == 0)
{
x_78 = x_28;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_28);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_20);
lean_dec_ref(x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_23, 0);
x_92 = !lean_is_exclusive(x_23);
if (x_92 == 0)
{
x_86 = x_23;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_23);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_dec_ref(x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_93 = lean_ctor_get(x_17, 0);
x_100 = !lean_is_exclusive(x_17);
if (x_100 == 0)
{
x_94 = x_17;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_17);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec_ref(x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_101 = lean_ctor_get(x_15, 0);
x_108 = !lean_is_exclusive(x_15);
if (x_108 == 0)
{
x_102 = x_15;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_15);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_7);
x_8 = lean_load_dynlib(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_132; 
x_7 = lean_ctor_get(x_6, 0);
x_132 = !lean_is_exclusive(x_6);
if (x_132 == 0)
{
x_8 = x_6;
x_9 = x_132;
goto block_131;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_10; 
x_10 = l_Lean_determineLakePath();
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_122; 
x_11 = lean_ctor_get(x_10, 0);
x_122 = !lean_is_exclusive(x_10);
if (x_122 == 0)
{
x_12 = x_10;
x_13 = x_122;
goto block_121;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_122;
goto block_121;
}
block_121:
{
uint8_t x_14; 
x_14 = l_System_FilePath_pathExists(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_del_object(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_15 = lean_box(1);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_11, x_7, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_112; 
x_20 = lean_ctor_get(x_19, 0);
x_112 = !lean_is_exclusive(x_19);
if (x_112 == 0)
{
x_21 = x_19;
x_22 = x_112;
goto block_111;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_23; uint32_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_48; uint8_t x_49; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get_uint32(x_20, sizeof(void*)*3);
x_25 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_23);
x_29 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__0));
x_30 = lean_array_to_list(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_String_intercalate(x_29, x_31);
x_48 = 0;
x_49 = lean_uint32_dec_eq(x_24, x_48);
if (x_49 == 0)
{
uint32_t x_50; uint8_t x_51; 
lean_del_object(x_21);
lean_del_object(x_8);
x_50 = 2;
x_51 = lean_uint32_dec_eq(x_24, x_50);
if (x_51 == 0)
{
uint32_t x_52; uint8_t x_53; 
x_52 = 3;
x_53 = lean_uint32_dec_eq(x_24, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__4));
x_55 = lean_string_append(x_54, x_32);
lean_dec_ref(x_32);
x_56 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__5));
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_string_append(x_57, x_25);
lean_dec_ref(x_25);
x_59 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_string_append(x_60, x_26);
lean_dec_ref(x_26);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_62);
x_63 = x_12;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_32);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_66 = lean_box(2);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_66);
x_67 = x_12;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_66);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_32);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_70 = lean_box(1);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_70);
x_71 = x_12;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
else
{
lean_object* x_74; 
lean_inc_ref(x_25);
x_74 = l_Lean_Json_parse(x_25);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_74);
lean_del_object(x_12);
goto block_47;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_instFromJsonModuleSetup_fromJson(x_75);
if (lean_obj_tag(x_76) == 1)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_110; 
lean_dec_ref(x_32);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_del_object(x_21);
lean_del_object(x_8);
x_77 = lean_ctor_get(x_76, 0);
x_110 = !lean_is_exclusive(x_76);
if (x_110 == 0)
{
x_78 = x_76;
x_79 = x_110;
goto block_109;
}
else
{
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_box(0);
x_79 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_87; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_77, 4);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_array_get_size(x_97);
x_100 = lean_nat_dec_lt(x_98, x_99);
if (x_100 == 0)
{
goto block_86;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_box(0);
x_102 = lean_nat_dec_le(x_99, x_99);
if (x_102 == 0)
{
if (x_100 == 0)
{
goto block_86;
}
else
{
size_t x_103; size_t x_104; lean_object* x_105; 
x_103 = 0;
x_104 = lean_usize_of_nat(x_99);
x_105 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(x_97, x_103, x_104, x_101);
x_87 = x_105;
goto block_96;
}
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_99);
x_108 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(x_97, x_106, x_107, x_101);
x_87 = x_108;
goto block_96;
}
}
block_86:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_77);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_80);
x_81 = x_12;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
block_96:
{
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
goto block_86;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_del_object(x_78);
lean_dec(x_77);
lean_del_object(x_12);
x_88 = lean_ctor_get(x_87, 0);
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
x_89 = x_87;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
else
{
lean_dec_ref(x_76);
lean_del_object(x_12);
goto block_47;
}
}
}
block_47:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__1));
x_34 = lean_string_append(x_33, x_32);
lean_dec_ref(x_32);
x_35 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__2));
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_25);
lean_dec_ref(x_25);
x_38 = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_26);
lean_dec_ref(x_26);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 0, x_40);
x_41 = x_8;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_40);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_41);
x_42 = x_21;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_del_object(x_12);
lean_del_object(x_8);
x_113 = lean_ctor_get(x_19, 0);
x_120 = !lean_is_exclusive(x_19);
if (x_120 == 0)
{
x_114 = x_19;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_dec(x_19);
x_114 = lean_box(0);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_115 == 0)
{
x_116 = x_114;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_130; 
lean_del_object(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_123 = lean_ctor_get(x_10, 0);
x_130 = !lean_is_exclusive(x_10);
if (x_130 == 0)
{
x_124 = x_10;
x_125 = x_130;
goto block_129;
}
else
{
lean_inc(x_123);
lean_dec(x_10);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_123);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_133 = lean_box(1);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_setupFile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Utils(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_LakePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_ServerTask(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Utils(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SetupFile(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_SetupFile(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_SetupFile(builtin);
}
#ifdef __cplusplus
}
#endif
