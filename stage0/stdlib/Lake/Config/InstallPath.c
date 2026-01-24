// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: public import Lean.Compiler.FFI public import Lake.Config.Dynlib public import Lake.Config.Defaults public import Lake.Util.NativeLib import Init.Data.String.Modify
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
lean_object* l_Lake_instReprDynlib_repr___redArg(lean_object*);
static lean_object* l_Lake_LakeInstall_ofLean___closed__3;
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__30;
static lean_object* l_Lake_LakeInstall_ofLean___closed__0;
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object*);
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__0;
extern lean_object* l_System_instInhabitedFilePath_default;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__16;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__17;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__19;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
extern lean_object* l_Lake_defaultBuildDir;
static lean_object* l_Lake_lakeExe___closed__0;
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object*);
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__36;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__14;
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__31;
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object*, lean_object*);
static lean_object* l_Lake_leanExe___closed__1;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__7;
static lean_object* l_Lake_envToBool_x3f___closed__19;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__46;
static lean_object* l_Lake_initSharedLib___closed__0;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanSharedLib;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__22;
static lean_object* l_Lake_getLakeInstall_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall;
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1;
lean_object* l_String_Slice_trimAscii(lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
static lean_object* l_Lake_findLeanSysroot_x3f___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__8;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__9;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__21;
lean_object* lean_io_getenv(lean_object*);
static lean_object* l_Lake_leanExe___closed__0;
static lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__3;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__5;
static lean_object* l_Lake_findInstall_x3f___closed__0;
static lean_object* l_Lake_findLeanSysroot_x3f___closed__2;
static lean_object* l_Lake_envToBool_x3f___closed__16;
static lean_object* l_Lake_envToBool_x3f___closed__11;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__13;
static lean_object* l_Lake_findLeanInstall_x3f___closed__0;
static lean_object* l_Lake_toolchain2Dir___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object*);
static lean_object* l_Lake_LeanInstall_get___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_leanCcExe___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__34;
lean_object* lean_string_length(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_envToBool_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall;
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__38;
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2;
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_envToBool_x3f___closed__18;
static lean_object* l_Lake_leanSharedLib___closed__0;
static lean_object* l_Lake_findLeanInstall_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall;
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object*);
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__20;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__18;
extern lean_object* l_Lake_sharedLibExt;
static lean_object* l_Lake_envToBool_x3f___closed__1;
static lean_object* l_Lake_envToBool_x3f___closed__7;
static lean_object* l_Lake_getLakeInstall_x3f___closed__2;
static lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__4;
static lean_object* l_Lake_lakeExe___closed__1;
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__24;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__18;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__35;
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_envToBool_x3f___closed__15;
static lean_object* l_Lake_envToBool_x3f___closed__10;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall_default;
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_envToBool_x3f___closed__13;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__20;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__10;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_Lake_LeanInstall_get___closed__4;
static lean_object* l_Lake_envToBool_x3f___closed__23;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object*);
static lean_object* l_Lake_LeanInstall_get___closed__3;
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall_default;
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object*);
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0;
static lean_object* l_Lake_LeanInstall_get___closed__0;
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LakeInstall_ofLean___closed__1;
static lean_object* l_Lake_leanSharedLib___closed__1;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__45;
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0;
static lean_object* l_Lake_envToBool_x3f___closed__20;
static lean_object* l_Lake_envToBool_x3f___closed__21;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__24;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_envToBool_x3f___closed__2;
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__32;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lake_instInhabitedElanInstall;
static lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__2;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__17;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__33;
static lean_object* l_Lake_envToBool_x3f___closed__14;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__28;
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__16;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__12;
static lean_object* l_Lake_findLeanSysroot_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f();
lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__27;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__9;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__2;
static lean_object* l_Lake_envToBool_x3f___closed__4;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_initSharedLib;
static lean_object* l_Lake_leanSharedLibDir___closed__0;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__6;
static lean_object* l_Lake_findElanInstall_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedElanInstall_default___closed__0;
static lean_object* l_Lake_findLeanSysroot_x3f___closed__4;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__19;
static lean_object* l_Lake_envToBool_x3f___closed__17;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object*);
static lean_object* l_Lake_LeanInstall_get___closed__1;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_envToBool_x3f___closed__9;
static lean_object* l_Lake_envToBool_x3f___closed__12;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__42;
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f();
LEAN_EXPORT lean_object* l_Lake_instInhabitedElanInstall_default;
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__4;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__41;
static lean_object* l_Lake_envToBool_x3f___closed__0;
static lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object*);
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__8;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__1;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__22;
lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0;
static lean_object* l_Lake_envToBool_x3f___closed__3;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object*);
static lean_object* l_Lake_instReprElanInstall___closed__0;
static lean_object* l_Lake_initSharedLib___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object*, lean_object*);
static lean_object* l_Lake_leancExe___closed__0;
static lean_object* l_Lake_envToBool_x3f___closed__5;
static lean_object* l_Lake_findElanInstall_x3f___closed__2;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object*);
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__44;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object*, lean_object*);
lean_object* lean_io_app_path();
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object*);
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__14;
static lean_object* l_Lake_getLakeInstall_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__15;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__23;
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeExe;
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f();
static lean_object* l_Lake_envToBool_x3f___closed__22;
static lean_object* l_Lake_leanArExe___closed__0;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__43;
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__29;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__23;
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object*, uint8_t);
extern lean_object* l_Lake_instInhabitedDynlib_default;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object*);
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__39;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__15;
uint32_t lean_uint32_add(uint32_t, uint32_t);
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__12;
static lean_object* l_Lake_envToBool_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_findLeanSysroot_x3f___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_LakeInstall_ofLean___closed__2;
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8;
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0;
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f();
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7;
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBinDir;
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object*);
static lean_object* l_Lake_instReprLakeInstall___closed__0;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object*);
static lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__0;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_LeanInstall_get___closed__5;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__3;
static lean_object* l_Lake_findLakeInstall_x3f___closed__0;
static lean_object* l_Lake_instReprLeanInstall___closed__0;
extern lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
extern lean_object* l_Lake_defaultLeanLibDir;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__37;
static lean_object* l_Lake_findElanInstall_x3f___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__40;
static lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__7;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__25;
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_string_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00Lake_envToBool_x3f_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_1, x_2);
x_12 = 65;
x_13 = lean_uint32_dec_le(x_12, x_11);
if (x_13 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 90;
x_15 = lean_uint32_dec_le(x_11, x_14);
if (x_15 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_16; uint32_t x_17; 
x_16 = 32;
x_17 = lean_uint32_add(x_11, x_16);
x_3 = x_17;
goto block_8;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_4 = lean_string_utf8_set(x_1, x_2, x_3);
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("y", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("yes", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("t", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("on", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_envToBool_x3f___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__6;
x_2 = l_Lake_envToBool_x3f___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__7;
x_2 = l_Lake_envToBool_x3f___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__8;
x_2 = l_Lake_envToBool_x3f___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__9;
x_2 = l_Lake_envToBool_x3f___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__10;
x_2 = l_Lake_envToBool_x3f___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("off", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_envToBool_x3f___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__18;
x_2 = l_Lake_envToBool_x3f___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__19;
x_2 = l_Lake_envToBool_x3f___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__20;
x_2 = l_Lake_envToBool_x3f___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__21;
x_2 = l_Lake_envToBool_x3f___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_envToBool_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_envToBool_x3f___closed__22;
x_2 = l_Lake_envToBool_x3f___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lake_envToBool_x3f___closed__11;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(x_1, x_3);
x_5 = l_List_elem___at___00Lake_envToBool_x3f_spec__1(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lake_envToBool_x3f___closed__23;
x_7 = l_List_elem___at___00Lake_envToBool_x3f_spec__1(x_4, x_6);
lean_dec_ref(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_4);
x_11 = lean_box(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_instInhabitedFilePath_default;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedElanInstall_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedElanInstall_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("home", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__5;
x_2 = l_Lake_instReprElanInstall_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elan", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchainsDir", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__21;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_instReprElanInstall_repr___redArg___closed__5;
x_7 = l_Lake_instReprElanInstall_repr___redArg___closed__6;
x_8 = l_Lake_instReprElanInstall_repr___redArg___closed__7;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lake_instReprElanInstall_repr___redArg___closed__9;
x_11 = l_String_quote(x_2);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Repr_addAppParen(x_13, x_9);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = 0;
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_instReprElanInstall_repr___redArg___closed__11;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_instReprElanInstall_repr___redArg___closed__13;
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_26 = l_String_quote(x_3);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_9);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_16);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_19);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
x_35 = l_Lake_instReprElanInstall_repr___redArg___closed__15;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
x_38 = l_Lake_instReprElanInstall_repr___redArg___closed__16;
x_39 = l_String_quote(x_4);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Repr_addAppParen(x_41, x_9);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_16);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_19);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_21);
x_48 = l_Lake_instReprElanInstall_repr___redArg___closed__18;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
x_51 = l_Lake_instReprElanInstall_repr___redArg___closed__19;
x_52 = l_String_quote(x_5);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_10);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Repr_addAppParen(x_54, x_9);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_16);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lake_instReprElanInstall_repr___redArg___closed__22;
x_60 = l_Lake_instReprElanInstall_repr___redArg___closed__23;
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = l_Lake_instReprElanInstall_repr___redArg___closed__24;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_16);
return x_65;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprElanInstall_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprElanInstall_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprElanInstall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprElanInstall_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprElanInstall() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprElanInstall___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("---", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_string_utf8_get_fast(x_1, x_3);
x_6 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_7 = 47;
x_8 = lean_uint32_dec_eq(x_5, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 58;
x_10 = lean_uint32_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_push(x_2, x_5);
x_2 = x_11;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0;
x_14 = lean_string_append(x_2, x_13);
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1;
x_17 = lean_string_append(x_2, x_16);
x_2 = x_17;
x_3 = x_6;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_toolchain2Dir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lake_toolchain2Dir___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_toolchain2Dir(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = l_Lake_toolchain2Dir___closed__0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(x_1, x_4, x_5);
x_7 = l_System_FilePath_join(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ElanInstall_toolchainDir(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_leanExe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_leanExe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lake_leanExe___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lake_leanExe___closed__1;
x_5 = l_System_FilePath_join(x_3, x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_leancExe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanc", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lake_leanExe___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lake_leancExe___closed__0;
x_5 = l_System_FilePath_join(x_3, x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_leanArExe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("llvm-ar", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lake_leanExe___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lake_leanArExe___closed__0;
x_5 = l_System_FilePath_join(x_3, x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_leanCcExe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clang", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lake_leanExe___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lake_leanCcExe___closed__0;
x_5 = l_System_FilePath_join(x_3, x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_leanSharedLibDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lake_leanSharedLibDir___closed__0;
x_4 = l_System_FilePath_join(x_1, x_3);
x_5 = l_Lake_leanExe___closed__1;
x_6 = l_System_FilePath_join(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lake_leanExe___closed__0;
x_8 = l_System_FilePath_join(x_1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libleanshared", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_sharedLibExt;
x_2 = l_Lake_leanSharedLib___closed__0;
x_3 = l_System_FilePath_addExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_leanSharedLib() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_leanSharedLib___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libInit_shared", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_sharedLibExt;
x_2 = l_Lake_initSharedLib___closed__0;
x_3 = l_System_FilePath_addExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initSharedLib() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initSharedLib___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_instInhabitedLeanInstall_default___closed__0;
x_2 = 0;
x_3 = l_Lake_toolchain2Dir___closed__0;
x_4 = l_System_instInhabitedFilePath_default;
x_5 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
lean_ctor_set(x_5, 7, x_4);
lean_ctor_set(x_5, 8, x_4);
lean_ctor_set(x_5, 9, x_4);
lean_ctor_set(x_5, 10, x_4);
lean_ctor_set(x_5, 11, x_4);
lean_ctor_set(x_5, 12, x_4);
lean_ctor_set(x_5, 13, x_1);
lean_ctor_set(x_5, 14, x_1);
lean_ctor_set(x_5, 15, x_1);
lean_ctor_set(x_5, 16, x_1);
lean_ctor_set(x_5, 17, x_1);
lean_ctor_set(x_5, 18, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*19, x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLeanInstall_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLeanInstall_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_String_quote(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_String_quote(x_11);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_String_quote(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(x_1, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_String_quote(x_11);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(x_1, x_16, x_12);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_quote(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lake_instReprElanInstall_repr___redArg___closed__11;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_array_to_list(x_1);
x_6 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1;
x_7 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(x_5, x_6);
x_8 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4;
x_9 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_Format_fill(x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8;
return x_15;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sysroot", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprElanInstall_repr___redArg___closed__5;
x_2 = l_Lake_instReprLeanInstall_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("githash", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("srcDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanLibDir", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("includeDir", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("systemLibDir", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_leanExe___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_leancExe___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sharedLib", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initSharedLib", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ar", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__25;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cc", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__28;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("customCc", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__30;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cFlags", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__33;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linkStaticFlags", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__35;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linkSharedFlags", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__38;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ccFlags", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__40;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ccLinkStaticFlags", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__42;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(21u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ccLinkSharedFlags", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLeanInstall_repr___redArg___closed__45;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 10);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 11);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
x_16 = lean_ctor_get(x_1, 13);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 14);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 15);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 16);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 17);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 18);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = l_Lake_instReprElanInstall_repr___redArg___closed__5;
x_23 = l_Lake_instReprLeanInstall_repr___redArg___closed__3;
x_24 = l_Lake_instReprLeanInstall_repr___redArg___closed__4;
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lake_instReprElanInstall_repr___redArg___closed__9;
x_27 = l_String_quote(x_2);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Repr_addAppParen(x_29, x_25);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lake_instReprElanInstall_repr___redArg___closed__11;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lake_instReprLeanInstall_repr___redArg___closed__6;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_22);
x_42 = l_String_quote(x_3);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_32);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_37);
x_49 = l_Lake_instReprLeanInstall_repr___redArg___closed__8;
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_22);
x_52 = l_Lake_instReprElanInstall_repr___redArg___closed__16;
x_53 = l_String_quote(x_4);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Repr_addAppParen(x_55, x_25);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_32);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_35);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_37);
x_62 = l_Lake_instReprLeanInstall_repr___redArg___closed__10;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_22);
x_65 = l_Lake_instReprLeanInstall_repr___redArg___closed__11;
x_66 = l_String_quote(x_5);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_26);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Repr_addAppParen(x_68, x_25);
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_32);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_35);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_37);
x_75 = l_Lake_instReprLeanInstall_repr___redArg___closed__13;
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_22);
x_78 = l_String_quote(x_6);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_26);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Repr_addAppParen(x_80, x_25);
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_32);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_35);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_37);
x_87 = l_Lake_instReprLeanInstall_repr___redArg___closed__15;
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_22);
x_90 = l_Lake_instReprLeanInstall_repr___redArg___closed__16;
x_91 = l_String_quote(x_7);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_26);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Repr_addAppParen(x_93, x_25);
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_32);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_35);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_37);
x_100 = l_Lake_instReprElanInstall_repr___redArg___closed__15;
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_22);
x_103 = l_String_quote(x_8);
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_26);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Repr_addAppParen(x_105, x_25);
x_107 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_107, 0, x_52);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_32);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_35);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_37);
x_112 = l_Lake_instReprLeanInstall_repr___redArg___closed__17;
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_22);
x_115 = l_Lake_instReprElanInstall_repr___redArg___closed__7;
x_116 = l_String_quote(x_9);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_26);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Repr_addAppParen(x_118, x_25);
x_120 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_32);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_35);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_37);
x_125 = l_Lake_instReprLeanInstall_repr___redArg___closed__18;
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_22);
x_128 = l_Lake_instReprLeanInstall_repr___redArg___closed__19;
x_129 = l_String_quote(x_10);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_26);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Repr_addAppParen(x_131, x_25);
x_133 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_32);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_35);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_37);
x_138 = l_Lake_instReprLeanInstall_repr___redArg___closed__21;
x_139 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_22);
x_141 = l_Lake_instReprLeanInstall_repr___redArg___closed__22;
x_142 = l_String_quote(x_11);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_26);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Repr_addAppParen(x_144, x_25);
x_146 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_146, 0, x_141);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_32);
x_148 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_35);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_37);
x_151 = l_Lake_instReprLeanInstall_repr___redArg___closed__24;
x_152 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_22);
x_154 = l_Lake_instReprElanInstall_repr___redArg___closed__19;
x_155 = l_String_quote(x_12);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_157, 0, x_26);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Repr_addAppParen(x_157, x_25);
x_159 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_32);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_153);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_35);
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_37);
x_164 = l_Lake_instReprLeanInstall_repr___redArg___closed__26;
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_22);
x_167 = l_Lake_instReprLeanInstall_repr___redArg___closed__27;
x_168 = l_String_quote(x_13);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_26);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Repr_addAppParen(x_170, x_25);
x_172 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_32);
x_174 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_174, 0, x_166);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_35);
x_176 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_37);
x_177 = l_Lake_instReprLeanInstall_repr___redArg___closed__29;
x_178 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_22);
x_180 = l_String_quote(x_14);
x_181 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Repr_addAppParen(x_182, x_25);
x_184 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_32);
x_186 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_35);
x_188 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_37);
x_189 = l_Lake_instReprLeanInstall_repr___redArg___closed__31;
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_22);
x_192 = l_Lake_instReprLeanInstall_repr___redArg___closed__32;
x_193 = l_Bool_repr___redArg(x_15);
x_194 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_32);
x_196 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_35);
x_198 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_37);
x_199 = l_Lake_instReprLeanInstall_repr___redArg___closed__34;
x_200 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_22);
x_202 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(x_16);
x_203 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_203, 0, x_52);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_32);
x_205 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_35);
x_207 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_37);
x_208 = l_Lake_instReprLeanInstall_repr___redArg___closed__36;
x_209 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_22);
x_211 = l_Lake_instReprLeanInstall_repr___redArg___closed__37;
x_212 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(x_17);
x_213 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_32);
x_215 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_35);
x_217 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_37);
x_218 = l_Lake_instReprLeanInstall_repr___redArg___closed__39;
x_219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_22);
x_221 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(x_18);
x_222 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_222, 0, x_211);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_32);
x_224 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_35);
x_226 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_37);
x_227 = l_Lake_instReprLeanInstall_repr___redArg___closed__41;
x_228 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_22);
x_230 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(x_19);
x_231 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_231, 0, x_24);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*1, x_32);
x_233 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_35);
x_235 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_37);
x_236 = l_Lake_instReprLeanInstall_repr___redArg___closed__43;
x_237 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_22);
x_239 = l_Lake_instReprLeanInstall_repr___redArg___closed__44;
x_240 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(x_20);
x_241 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_32);
x_243 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_243, 0, x_238);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_35);
x_245 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_37);
x_246 = l_Lake_instReprLeanInstall_repr___redArg___closed__46;
x_247 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_22);
x_249 = l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(x_21);
x_250 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_250, 0, x_239);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_32);
x_252 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_252, 0, x_248);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lake_instReprElanInstall_repr___redArg___closed__22;
x_254 = l_Lake_instReprElanInstall_repr___redArg___closed__23;
x_255 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
x_256 = l_Lake_instReprElanInstall_repr___redArg___closed__24;
x_257 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_32);
return x_259;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprLeanInstall_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprLeanInstall_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprLeanInstall_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprLeanInstall___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 5);
x_5 = lean_box(0);
lean_inc_ref(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_box(0);
lean_inc_ref(x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanInstall_sharedLibPath(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 12);
lean_inc_ref(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanInstall_leanCc_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 17);
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 18);
lean_inc_ref(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_LeanInstall_ccLinkFlags(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_exeExtension;
x_2 = l_Lake_lakeExe___closed__0;
x_3 = l_System_FilePath_addExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_lakeExe() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_lakeExe___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instInhabitedDynlib_default;
x_2 = l_System_instInhabitedFilePath_default;
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLakeInstall_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLakeInstall_default;
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLakeInstall_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sharedDynlib", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprLakeInstall_repr___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_lakeExe___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lake_instReprElanInstall_repr___redArg___closed__5;
x_9 = l_Lake_instReprElanInstall_repr___redArg___closed__6;
x_10 = l_Lake_instReprElanInstall_repr___redArg___closed__7;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lake_instReprElanInstall_repr___redArg___closed__9;
x_13 = l_String_quote(x_2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_11);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lake_instReprElanInstall_repr___redArg___closed__11;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lake_instReprLeanInstall_repr___redArg___closed__8;
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
x_28 = l_Lake_instReprElanInstall_repr___redArg___closed__16;
x_29 = l_String_quote(x_3);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Repr_addAppParen(x_31, x_11);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_18);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
x_38 = l_Lake_instReprElanInstall_repr___redArg___closed__15;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
x_41 = l_String_quote(x_4);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Repr_addAppParen(x_43, x_11);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_18);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_21);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_23);
x_50 = l_Lake_instReprLakeInstall_repr___redArg___closed__1;
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
x_53 = l_String_quote(x_5);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_12);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Repr_addAppParen(x_55, x_11);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_18);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_21);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_23);
x_62 = l_Lake_instReprLakeInstall_repr___redArg___closed__3;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
x_65 = l_Lake_instReprLeanInstall_repr___redArg___closed__16;
x_66 = l_Lake_instReprDynlib_repr___redArg(x_6);
x_67 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_18);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_21);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_23);
x_72 = l_Lake_instReprLakeInstall_repr___redArg___closed__4;
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_8);
x_75 = l_String_quote(x_7);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Repr_addAppParen(x_77, x_11);
x_79 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_18);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lake_instReprElanInstall_repr___redArg___closed__22;
x_83 = l_Lake_instReprElanInstall_repr___redArg___closed__23;
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
x_85 = l_Lake_instReprElanInstall_repr___redArg___closed__24;
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_18);
return x_88;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprLakeInstall_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprLakeInstall_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprLakeInstall_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprLakeInstall___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LakeInstall_sharedLib(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake_shared", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libLake_shared.", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_sharedLibExt;
x_2 = l_Lake_LakeInstall_ofLean___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_17; uint8_t x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_lakeExe___closed__0;
x_7 = l_System_FilePath_join(x_3, x_6);
x_17 = l_Lake_LakeInstall_ofLean___closed__3;
x_18 = l_System_Platform_isWindows;
if (x_18 == 0)
{
lean_object* x_19; 
lean_inc_ref(x_4);
x_19 = l_System_FilePath_join(x_4, x_17);
x_8 = x_19;
goto block_16;
}
else
{
lean_object* x_20; 
lean_inc_ref(x_5);
x_20 = l_System_FilePath_join(x_5, x_17);
x_8 = x_20;
goto block_16;
}
block_16:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lake_LakeInstall_ofLean___closed__0;
x_10 = 0;
x_11 = l_Lake_LakeInstall_ofLean___closed__1;
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_10);
x_13 = l_Lake_lakeExe;
lean_inc_ref(x_5);
x_14 = l_System_FilePath_join(x_5, x_13);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_5);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set(x_15, 5, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lake_findElanInstall_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN_HOME", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_findElanInstall_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ELAN", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_findElanInstall_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toolchains", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_findElanInstall_x3f___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_5 = x_3;
} else {
 lean_dec_ref(x_3);
 x_5 = lean_box(0);
}
x_6 = l_Lake_findElanInstall_x3f___closed__1;
x_7 = lean_io_getenv(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_25; 
x_25 = l_Lake_instReprElanInstall_repr___redArg___closed__12;
x_8 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec_ref(x_7);
x_8 = x_26;
goto block_24;
}
block_24:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_byte_size(x_8);
lean_inc_ref(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_String_Slice_trimAscii(x_11);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_nat_sub(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
x_16 = lean_nat_dec_eq(x_15, x_9);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Lake_leanExe___closed__0;
lean_inc(x_4);
x_18 = l_System_FilePath_join(x_4, x_17);
x_19 = l_Lake_findElanInstall_x3f___closed__2;
lean_inc(x_4);
x_20 = l_System_FilePath_join(x_4, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
if (lean_is_scalar(x_5)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_5;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_3);
x_27 = lean_box(0);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_findElanInstall_x3f();
return x_2;
}
}
static lean_object* _init_l_Lake_findLeanSysroot_x3f___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_findLeanSysroot_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--print-prefix", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_findLeanSysroot_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_findLeanSysroot_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_findLeanSysroot_x3f___closed__1;
x_2 = l_Lake_findLeanSysroot_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_findLeanSysroot_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lake_findLeanSysroot_x3f___closed__0;
x_4 = l_Lake_findLeanSysroot_x3f___closed__3;
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lake_findLeanSysroot_x3f___closed__4;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_4);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_IO_Process_output(x_10, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint32(x_13, sizeof(void*)*2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = lean_uint32_dec_eq(x_14, x_16);
if (x_17 == 0)
{
lean_dec_ref(x_15);
lean_free_object(x_11);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_string_utf8_byte_size(x_15);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_String_Slice_trimAscii(x_19);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_string_utf8_extract(x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; uint32_t x_26; lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get_uint32(x_25, sizeof(void*)*2);
x_27 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = lean_uint32_dec_eq(x_26, x_28);
if (x_29 == 0)
{
lean_dec_ref(x_27);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_string_utf8_byte_size(x_27);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_31, 2, x_30);
x_32 = l_String_Slice_trimAscii(x_31);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 2);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_string_utf8_extract(x_33, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_dec_ref(x_11);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_findLeanSysroot_x3f(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--githash", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0;
x_2 = l_Lake_findLeanSysroot_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lake_findLeanSysroot_x3f___closed__0;
x_4 = l_Lake_leanExe(x_1);
x_5 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1;
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lake_findLeanSysroot_x3f___closed__4;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = l_IO_Process_output(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_string_utf8_byte_size(x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_String_Slice_trimAscii(x_16);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = lean_string_utf8_extract(x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_12);
x_22 = l_Lake_toolchain2Dir___closed__0;
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("AR", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0;
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_6 = l_Lake_leanArExe(x_1);
x_7 = l_System_FilePath_pathExists(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_6);
x_8 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1;
x_9 = lean_io_getenv(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = l_Lake_instReprLeanInstall_repr___redArg___closed__25;
return x_11;
}
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_2, 13);
x_6 = lean_ctor_get(x_2, 14);
x_7 = lean_ctor_get(x_2, 15);
x_8 = lean_ctor_get(x_2, 18);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 17);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 16);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 12);
lean_dec(x_11);
x_12 = l_Lean_Compiler_FFI_getInternalLinkerFlags(x_1);
x_13 = 0;
x_14 = l_Lean_Compiler_FFI_getInternalCFlags(x_1);
lean_inc_ref(x_5);
x_15 = l_Array_append___redArg(x_5, x_14);
lean_dec_ref(x_14);
lean_inc_ref(x_12);
x_16 = l_Array_append___redArg(x_12, x_6);
x_17 = l_Array_append___redArg(x_12, x_7);
lean_ctor_set(x_2, 18, x_17);
lean_ctor_set(x_2, 17, x_16);
lean_ctor_set(x_2, 16, x_15);
lean_ctor_set(x_2, 12, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*19, x_13);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
x_24 = lean_ctor_get(x_2, 6);
x_25 = lean_ctor_get(x_2, 7);
x_26 = lean_ctor_get(x_2, 8);
x_27 = lean_ctor_get(x_2, 9);
x_28 = lean_ctor_get(x_2, 10);
x_29 = lean_ctor_get(x_2, 11);
x_30 = lean_ctor_get(x_2, 13);
x_31 = lean_ctor_get(x_2, 14);
x_32 = lean_ctor_get(x_2, 15);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_33 = l_Lean_Compiler_FFI_getInternalLinkerFlags(x_1);
x_34 = 0;
x_35 = l_Lean_Compiler_FFI_getInternalCFlags(x_1);
lean_inc_ref(x_30);
x_36 = l_Array_append___redArg(x_30, x_35);
lean_dec_ref(x_35);
lean_inc_ref(x_33);
x_37 = l_Array_append___redArg(x_33, x_31);
x_38 = l_Array_append___redArg(x_33, x_32);
x_39 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_39, 2, x_20);
lean_ctor_set(x_39, 3, x_21);
lean_ctor_set(x_39, 4, x_22);
lean_ctor_set(x_39, 5, x_23);
lean_ctor_set(x_39, 6, x_24);
lean_ctor_set(x_39, 7, x_25);
lean_ctor_set(x_39, 8, x_26);
lean_ctor_set(x_39, 9, x_27);
lean_ctor_set(x_39, 10, x_28);
lean_ctor_set(x_39, 11, x_29);
lean_ctor_set(x_39, 12, x_3);
lean_ctor_set(x_39, 13, x_30);
lean_ctor_set(x_39, 14, x_31);
lean_ctor_set(x_39, 15, x_32);
lean_ctor_set(x_39, 16, x_36);
lean_ctor_set(x_39, 17, x_37);
lean_ctor_set(x_39, 18, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*19, x_34);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 12);
lean_dec(x_4);
lean_ctor_set(x_1, 12, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get(x_1, 6);
x_12 = lean_ctor_get(x_1, 7);
x_13 = lean_ctor_get(x_1, 8);
x_14 = lean_ctor_get(x_1, 9);
x_15 = lean_ctor_get(x_1, 10);
x_16 = lean_ctor_get(x_1, 11);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
x_18 = lean_ctor_get(x_1, 13);
x_19 = lean_ctor_get(x_1, 14);
x_20 = lean_ctor_get(x_1, 15);
x_21 = lean_ctor_get(x_1, 16);
x_22 = lean_ctor_get(x_1, 17);
x_23 = lean_ctor_get(x_1, 18);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
lean_ctor_set(x_24, 3, x_8);
lean_ctor_set(x_24, 4, x_9);
lean_ctor_set(x_24, 5, x_10);
lean_ctor_set(x_24, 6, x_11);
lean_ctor_set(x_24, 7, x_12);
lean_ctor_set(x_24, 8, x_13);
lean_ctor_set(x_24, 9, x_14);
lean_ctor_set(x_24, 10, x_15);
lean_ctor_set(x_24, 11, x_16);
lean_ctor_set(x_24, 12, x_2);
lean_ctor_set(x_24, 13, x_18);
lean_ctor_set(x_24, 14, x_19);
lean_ctor_set(x_24, 15, x_20);
lean_ctor_set(x_24, 16, x_21);
lean_ctor_set(x_24, 17, x_22);
lean_ctor_set(x_24, 18, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*19, x_17);
return x_24;
}
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_CC", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CC", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0;
x_30 = lean_io_getenv(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_4 = x_31;
x_5 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_30);
lean_inc_ref(x_1);
x_32 = l_Lake_leanCcExe(x_1);
x_33 = l_System_FilePath_pathExists(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_32);
lean_dec_ref(x_1);
x_34 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1;
x_35 = lean_io_getenv(x_34);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_4 = x_36;
x_5 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_37; 
lean_dec(x_35);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 12);
lean_dec(x_38);
x_39 = l_Lake_instReprLeanInstall_repr___redArg___closed__28;
lean_ctor_set(x_2, 12, x_39);
return x_2;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_ctor_get(x_2, 4);
x_45 = lean_ctor_get(x_2, 5);
x_46 = lean_ctor_get(x_2, 6);
x_47 = lean_ctor_get(x_2, 7);
x_48 = lean_ctor_get(x_2, 8);
x_49 = lean_ctor_get(x_2, 9);
x_50 = lean_ctor_get(x_2, 10);
x_51 = lean_ctor_get(x_2, 11);
x_52 = lean_ctor_get_uint8(x_2, sizeof(void*)*19);
x_53 = lean_ctor_get(x_2, 13);
x_54 = lean_ctor_get(x_2, 14);
x_55 = lean_ctor_get(x_2, 15);
x_56 = lean_ctor_get(x_2, 16);
x_57 = lean_ctor_get(x_2, 17);
x_58 = lean_ctor_get(x_2, 18);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_59 = l_Lake_instReprLeanInstall_repr___redArg___closed__28;
x_60 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_60, 0, x_40);
lean_ctor_set(x_60, 1, x_41);
lean_ctor_set(x_60, 2, x_42);
lean_ctor_set(x_60, 3, x_43);
lean_ctor_set(x_60, 4, x_44);
lean_ctor_set(x_60, 5, x_45);
lean_ctor_set(x_60, 6, x_46);
lean_ctor_set(x_60, 7, x_47);
lean_ctor_set(x_60, 8, x_48);
lean_ctor_set(x_60, 9, x_49);
lean_ctor_set(x_60, 10, x_50);
lean_ctor_set(x_60, 11, x_51);
lean_ctor_set(x_60, 12, x_59);
lean_ctor_set(x_60, 13, x_53);
lean_ctor_set(x_60, 14, x_54);
lean_ctor_set(x_60, 15, x_55);
lean_ctor_set(x_60, 16, x_56);
lean_ctor_set(x_60, 17, x_57);
lean_ctor_set(x_60, 18, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*19, x_52);
return x_60;
}
}
}
else
{
lean_object* x_61; 
x_61 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(x_1, x_2, x_32);
lean_dec_ref(x_1);
return x_61;
}
}
block_28:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 12);
lean_dec(x_7);
lean_ctor_set(x_2, 12, x_4);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 8);
x_17 = lean_ctor_get(x_2, 9);
x_18 = lean_ctor_get(x_2, 10);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*19);
x_21 = lean_ctor_get(x_2, 13);
x_22 = lean_ctor_get(x_2, 14);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_11);
lean_ctor_set(x_27, 4, x_12);
lean_ctor_set(x_27, 5, x_13);
lean_ctor_set(x_27, 6, x_14);
lean_ctor_set(x_27, 7, x_15);
lean_ctor_set(x_27, 8, x_16);
lean_ctor_set(x_27, 9, x_17);
lean_ctor_set(x_27, 10, x_18);
lean_ctor_set(x_27, 11, x_19);
lean_ctor_set(x_27, 12, x_4);
lean_ctor_set(x_27, 13, x_21);
lean_ctor_set(x_27, 14, x_22);
lean_ctor_set(x_27, 15, x_23);
lean_ctor_set(x_27, 16, x_24);
lean_ctor_set(x_27, 17, x_25);
lean_ctor_set(x_27, 18, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*19, x_20);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("src", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("include", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wno-unused-command-line-argument", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanInstall_get___closed__2;
x_2 = l_Lean_Compiler_FFI_getCFlags_x27;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (x_2 == 0)
{
lean_object* x_33; 
lean_inc_ref(x_1);
x_33 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(x_1);
x_4 = x_33;
x_5 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_githash;
x_4 = x_34;
x_5 = lean_box(0);
goto block_32;
}
block_32:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_1);
x_6 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(x_1);
x_7 = l_Lake_LeanInstall_get___closed__0;
lean_inc_ref(x_1);
x_8 = l_System_FilePath_join(x_1, x_7);
x_9 = l_Lake_leanExe___closed__1;
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = l_Lake_leanSharedLibDir___closed__0;
lean_inc_ref(x_1);
x_12 = l_System_FilePath_join(x_1, x_11);
lean_inc_ref(x_12);
x_13 = l_System_FilePath_join(x_12, x_9);
x_14 = l_Lake_LeanInstall_get___closed__1;
lean_inc_ref(x_1);
x_15 = l_System_FilePath_join(x_1, x_14);
x_16 = l_Lake_leanExe___closed__0;
lean_inc_ref(x_1);
x_17 = l_System_FilePath_join(x_1, x_16);
lean_inc_ref(x_1);
x_18 = l_Lake_leanExe(x_1);
lean_inc_ref(x_1);
x_19 = l_Lake_leancExe(x_1);
lean_inc_ref(x_1);
x_20 = l_Lake_leanSharedLibDir(x_1);
x_21 = l_Lake_leanSharedLib;
lean_inc_ref(x_20);
x_22 = l_System_FilePath_join(x_20, x_21);
x_23 = l_Lake_initSharedLib;
x_24 = l_System_FilePath_join(x_20, x_23);
x_25 = l_Lake_instReprLeanInstall_repr___redArg___closed__28;
x_26 = 1;
x_27 = l_Lake_LeanInstall_get___closed__3;
x_28 = l_Lake_LeanInstall_get___closed__4;
x_29 = l_Lake_LeanInstall_get___closed__5;
lean_inc_ref(x_1);
x_30 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_10);
lean_ctor_set(x_30, 3, x_13);
lean_ctor_set(x_30, 4, x_15);
lean_ctor_set(x_30, 5, x_12);
lean_ctor_set(x_30, 6, x_17);
lean_ctor_set(x_30, 7, x_18);
lean_ctor_set(x_30, 8, x_19);
lean_ctor_set(x_30, 9, x_22);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_6);
lean_ctor_set(x_30, 12, x_25);
lean_ctor_set(x_30, 13, x_27);
lean_ctor_set(x_30, 14, x_28);
lean_ctor_set(x_30, 15, x_29);
lean_ctor_set(x_30, 16, x_27);
lean_ctor_set(x_30, 17, x_28);
lean_ctor_set(x_30, 18, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*19, x_26);
x_31 = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(x_1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lake_LeanInstall_get(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_findLeanSysroot_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = 0;
x_8 = l_Lake_LeanInstall_get(x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = 0;
x_11 = l_Lake_LeanInstall_get(x_9, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_findLeanCmdInstall_x3f(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f() {
_start:
{
lean_object* x_2; lean_object* x_5; 
x_5 = lean_io_app_path();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_System_FilePath_parent(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lake_leanExe___closed__1;
lean_inc(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = l_System_FilePath_exeExtension;
x_12 = l_System_FilePath_addExtension(x_10, x_11);
x_13 = l_System_FilePath_pathExists(x_12);
lean_dec_ref(x_12);
if (x_13 == 0)
{
lean_dec(x_8);
x_2 = lean_box(0);
goto block_4;
}
else
{
lean_object* x_14; 
x_14 = l_System_FilePath_parent(x_8);
return x_14;
}
}
else
{
lean_dec(x_7);
x_2 = lean_box(0);
goto block_4;
}
}
else
{
lean_dec_ref(x_5);
x_2 = lean_box(0);
goto block_4;
}
block_4:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_findLakeLeanJointHome_x3f();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = l_System_FilePath_parent(x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_System_FilePath_parent(x_5);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_parent(x_7);
return x_8;
}
}
}
}
}
static lean_object* _init_l_Lake_getLakeInstall_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_getLakeInstall_x3f___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_getLakeInstall_x3f___closed__0;
x_3 = l_Lake_nameToSharedLib(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_getLakeInstall_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.olean", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_Lake_lakeBuildHome_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_defaultBuildDir;
lean_inc(x_5);
x_7 = l_System_FilePath_join(x_5, x_6);
x_8 = l_Lake_defaultBinDir;
lean_inc_ref(x_7);
x_9 = l_System_FilePath_join(x_7, x_8);
x_10 = l_Lake_defaultLeanLibDir;
x_11 = l_System_FilePath_join(x_7, x_10);
x_12 = l_Lake_getLakeInstall_x3f___closed__0;
x_13 = 0;
x_14 = l_Lake_getLakeInstall_x3f___closed__1;
lean_inc_ref(x_11);
x_15 = l_System_FilePath_join(x_11, x_14);
x_16 = l_Lake_LakeInstall_ofLean___closed__1;
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_13);
lean_inc_ref(x_11);
lean_inc(x_5);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_11);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_1);
x_19 = l_Lake_getLakeInstall_x3f___closed__2;
x_20 = l_System_FilePath_join(x_11, x_19);
x_21 = l_System_FilePath_pathExists(x_20);
lean_dec_ref(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_18);
lean_free_object(x_3);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lake_defaultBuildDir;
lean_inc(x_23);
x_25 = l_System_FilePath_join(x_23, x_24);
x_26 = l_Lake_defaultBinDir;
lean_inc_ref(x_25);
x_27 = l_System_FilePath_join(x_25, x_26);
x_28 = l_Lake_defaultLeanLibDir;
x_29 = l_System_FilePath_join(x_25, x_28);
x_30 = l_Lake_getLakeInstall_x3f___closed__0;
x_31 = 0;
x_32 = l_Lake_getLakeInstall_x3f___closed__1;
lean_inc_ref(x_29);
x_33 = l_System_FilePath_join(x_29, x_32);
x_34 = l_Lake_LakeInstall_ofLean___closed__1;
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_31);
lean_inc_ref(x_29);
lean_inc(x_23);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_1);
x_37 = l_Lake_getLakeInstall_x3f___closed__2;
x_38 = l_System_FilePath_join(x_29, x_37);
x_39 = l_System_FilePath_pathExists(x_38);
lean_dec_ref(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_36);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_42 = lean_box(0);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getLakeInstall_x3f(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_findLeanInstall_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_findLeanInstall_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_findLeanInstall_x3f___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = 0;
x_7 = l_Lake_LeanInstall_get(x_5, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = 0;
x_10 = l_Lake_LeanInstall_get(x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_12 = l_Lake_findLeanInstall_x3f___closed__1;
x_13 = lean_io_getenv(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec_ref(x_13);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_string_utf8_byte_size(x_26);
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_String_Slice_trimAscii(x_29);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_nat_sub(x_32, x_31);
lean_dec(x_31);
lean_dec(x_32);
x_34 = lean_nat_dec_eq(x_33, x_27);
lean_dec(x_33);
if (x_34 == 0)
{
x_14 = x_26;
goto block_25;
}
else
{
lean_object* x_35; 
lean_dec(x_26);
x_35 = lean_box(0);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_13);
x_36 = l_Lake_leanExe___closed__1;
x_14 = x_36;
goto block_25;
}
block_25:
{
lean_object* x_15; 
x_15 = l_Lake_findLeanSysroot_x3f(x_14);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = 0;
x_19 = l_Lake_LeanInstall_get(x_17, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = 0;
x_22 = l_Lake_LeanInstall_get(x_20, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_15);
x_24 = lean_box(0);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_findLeanInstall_x3f();
return x_2;
}
}
static lean_object* _init_l_Lake_findLakeInstall_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f() {
_start:
{
lean_object* x_2; lean_object* x_41; 
x_41 = lean_io_app_path();
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lake_getLakeInstall_x3f(x_42);
if (lean_obj_tag(x_43) == 1)
{
return x_43;
}
else
{
lean_dec(x_43);
x_2 = lean_box(0);
goto block_40;
}
}
else
{
lean_dec_ref(x_41);
x_2 = lean_box(0);
goto block_40;
}
block_40:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_findLakeInstall_x3f___closed__0;
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lake_defaultBuildDir;
lean_inc(x_6);
x_8 = l_System_FilePath_join(x_6, x_7);
x_9 = l_Lake_defaultBinDir;
lean_inc_ref(x_8);
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = l_Lake_defaultLeanLibDir;
x_12 = l_System_FilePath_join(x_8, x_11);
x_13 = l_Lake_getLakeInstall_x3f___closed__0;
x_14 = 0;
x_15 = l_Lake_getLakeInstall_x3f___closed__1;
lean_inc_ref(x_12);
x_16 = l_System_FilePath_join(x_12, x_15);
x_17 = l_Lake_LakeInstall_ofLean___closed__1;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_14);
x_19 = l_Lake_lakeExe;
lean_inc_ref(x_10);
x_20 = l_System_FilePath_join(x_10, x_19);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_10);
lean_ctor_set(x_21, 3, x_12);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = l_Lake_defaultBuildDir;
lean_inc(x_22);
x_24 = l_System_FilePath_join(x_22, x_23);
x_25 = l_Lake_defaultBinDir;
lean_inc_ref(x_24);
x_26 = l_System_FilePath_join(x_24, x_25);
x_27 = l_Lake_defaultLeanLibDir;
x_28 = l_System_FilePath_join(x_24, x_27);
x_29 = l_Lake_getLakeInstall_x3f___closed__0;
x_30 = 0;
x_31 = l_Lake_getLakeInstall_x3f___closed__1;
lean_inc_ref(x_28);
x_32 = l_System_FilePath_join(x_28, x_31);
x_33 = l_Lake_LakeInstall_ofLean___closed__1;
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_30);
x_35 = l_Lake_lakeExe;
lean_inc_ref(x_26);
x_36 = l_System_FilePath_join(x_26, x_35);
lean_inc(x_22);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_34);
lean_ctor_set(x_37, 5, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_4);
x_39 = lean_box(0);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_findLakeInstall_x3f();
return x_2;
}
}
static lean_object* _init_l_Lake_findInstall_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_OVERRIDE_LEAN", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_findElanInstall_x3f();
x_3 = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_5 = x_3;
} else {
 lean_dec_ref(x_3);
 x_5 = lean_box(0);
}
x_6 = l_Lake_findInstall_x3f___closed__0;
x_7 = lean_io_getenv(x_6);
if (lean_obj_tag(x_7) == 0)
{
goto block_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = l_Lake_envToBool_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
goto block_15;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_free_object(x_17);
lean_dec(x_19);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
x_21 = l_Lake_toolchain2Dir___closed__0;
x_22 = l_Lake_LeanInstall_get___closed__0;
lean_inc(x_4);
x_23 = l_System_FilePath_join(x_4, x_22);
x_24 = l_Lake_leanExe___closed__1;
x_25 = l_System_FilePath_join(x_23, x_24);
x_26 = l_Lake_leanSharedLibDir___closed__0;
lean_inc(x_4);
x_27 = l_System_FilePath_join(x_4, x_26);
lean_inc_ref(x_27);
x_28 = l_System_FilePath_join(x_27, x_24);
x_29 = l_Lake_LeanInstall_get___closed__1;
lean_inc(x_4);
x_30 = l_System_FilePath_join(x_4, x_29);
x_31 = l_Lake_leanExe___closed__0;
lean_inc(x_4);
x_32 = l_System_FilePath_join(x_4, x_31);
lean_inc(x_4);
x_33 = l_Lake_leanExe(x_4);
lean_inc(x_4);
x_34 = l_Lake_leancExe(x_4);
lean_inc(x_4);
x_35 = l_Lake_leanSharedLibDir(x_4);
x_36 = l_Lake_leanSharedLib;
lean_inc_ref(x_35);
x_37 = l_System_FilePath_join(x_35, x_36);
x_38 = l_Lake_initSharedLib;
x_39 = l_System_FilePath_join(x_35, x_38);
x_40 = l_Lake_instReprLeanInstall_repr___redArg___closed__25;
x_41 = l_Lake_instReprLeanInstall_repr___redArg___closed__28;
x_42 = l_Lake_LeanInstall_get___closed__3;
x_43 = lean_unbox(x_19);
x_44 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_43);
x_45 = l_Lake_LeanInstall_get___closed__5;
lean_inc_ref(x_44);
x_46 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_21);
lean_ctor_set(x_46, 2, x_25);
lean_ctor_set(x_46, 3, x_28);
lean_ctor_set(x_46, 4, x_30);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_32);
lean_ctor_set(x_46, 7, x_33);
lean_ctor_set(x_46, 8, x_34);
lean_ctor_set(x_46, 9, x_37);
lean_ctor_set(x_46, 10, x_39);
lean_ctor_set(x_46, 11, x_40);
lean_ctor_set(x_46, 12, x_41);
lean_ctor_set(x_46, 13, x_42);
lean_ctor_set(x_46, 14, x_44);
lean_ctor_set(x_46, 15, x_45);
lean_ctor_set(x_46, 16, x_42);
lean_ctor_set(x_46, 17, x_44);
lean_ctor_set(x_46, 18, x_45);
x_47 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*19, x_47);
x_48 = l_Lake_findLeanInstall_x3f();
x_49 = l_Lake_LakeInstall_ofLean(x_46);
lean_ctor_set(x_17, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_17);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_17, 0);
lean_inc(x_52);
lean_dec(x_17);
x_53 = lean_unbox(x_52);
if (x_53 == 0)
{
lean_dec(x_52);
goto block_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_5);
x_54 = l_Lake_toolchain2Dir___closed__0;
x_55 = l_Lake_LeanInstall_get___closed__0;
lean_inc(x_4);
x_56 = l_System_FilePath_join(x_4, x_55);
x_57 = l_Lake_leanExe___closed__1;
x_58 = l_System_FilePath_join(x_56, x_57);
x_59 = l_Lake_leanSharedLibDir___closed__0;
lean_inc(x_4);
x_60 = l_System_FilePath_join(x_4, x_59);
lean_inc_ref(x_60);
x_61 = l_System_FilePath_join(x_60, x_57);
x_62 = l_Lake_LeanInstall_get___closed__1;
lean_inc(x_4);
x_63 = l_System_FilePath_join(x_4, x_62);
x_64 = l_Lake_leanExe___closed__0;
lean_inc(x_4);
x_65 = l_System_FilePath_join(x_4, x_64);
lean_inc(x_4);
x_66 = l_Lake_leanExe(x_4);
lean_inc(x_4);
x_67 = l_Lake_leancExe(x_4);
lean_inc(x_4);
x_68 = l_Lake_leanSharedLibDir(x_4);
x_69 = l_Lake_leanSharedLib;
lean_inc_ref(x_68);
x_70 = l_System_FilePath_join(x_68, x_69);
x_71 = l_Lake_initSharedLib;
x_72 = l_System_FilePath_join(x_68, x_71);
x_73 = l_Lake_instReprLeanInstall_repr___redArg___closed__25;
x_74 = l_Lake_instReprLeanInstall_repr___redArg___closed__28;
x_75 = l_Lake_LeanInstall_get___closed__3;
x_76 = lean_unbox(x_52);
x_77 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_76);
x_78 = l_Lake_LeanInstall_get___closed__5;
lean_inc_ref(x_77);
x_79 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_54);
lean_ctor_set(x_79, 2, x_58);
lean_ctor_set(x_79, 3, x_61);
lean_ctor_set(x_79, 4, x_63);
lean_ctor_set(x_79, 5, x_60);
lean_ctor_set(x_79, 6, x_65);
lean_ctor_set(x_79, 7, x_66);
lean_ctor_set(x_79, 8, x_67);
lean_ctor_set(x_79, 9, x_70);
lean_ctor_set(x_79, 10, x_72);
lean_ctor_set(x_79, 11, x_73);
lean_ctor_set(x_79, 12, x_74);
lean_ctor_set(x_79, 13, x_75);
lean_ctor_set(x_79, 14, x_77);
lean_ctor_set(x_79, 15, x_78);
lean_ctor_set(x_79, 16, x_75);
lean_ctor_set(x_79, 17, x_77);
lean_ctor_set(x_79, 18, x_78);
x_80 = lean_unbox(x_52);
lean_dec(x_52);
lean_ctor_set_uint8(x_79, sizeof(void*)*19, x_80);
x_81 = l_Lake_findLeanInstall_x3f();
x_82 = l_Lake_LakeInstall_ofLean(x_79);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
block_15:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = 1;
x_9 = l_Lake_LeanInstall_get(x_4, x_8);
lean_inc_ref(x_9);
x_10 = l_Lake_LakeInstall_ofLean(x_9);
if (lean_is_scalar(x_5)) {
 x_11 = lean_alloc_ctor(1, 1, 0);
} else {
 x_11 = x_5;
}
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_86 = l_Lake_findLeanInstall_x3f();
x_87 = l_Lake_findLakeInstall_x3f();
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_findInstall_x3f();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_envToBool_x3f___closed__0 = _init_l_Lake_envToBool_x3f___closed__0();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__0);
l_Lake_envToBool_x3f___closed__1 = _init_l_Lake_envToBool_x3f___closed__1();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__1);
l_Lake_envToBool_x3f___closed__2 = _init_l_Lake_envToBool_x3f___closed__2();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__2);
l_Lake_envToBool_x3f___closed__3 = _init_l_Lake_envToBool_x3f___closed__3();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__3);
l_Lake_envToBool_x3f___closed__4 = _init_l_Lake_envToBool_x3f___closed__4();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__4);
l_Lake_envToBool_x3f___closed__5 = _init_l_Lake_envToBool_x3f___closed__5();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__5);
l_Lake_envToBool_x3f___closed__6 = _init_l_Lake_envToBool_x3f___closed__6();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__6);
l_Lake_envToBool_x3f___closed__7 = _init_l_Lake_envToBool_x3f___closed__7();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__7);
l_Lake_envToBool_x3f___closed__8 = _init_l_Lake_envToBool_x3f___closed__8();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__8);
l_Lake_envToBool_x3f___closed__9 = _init_l_Lake_envToBool_x3f___closed__9();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__9);
l_Lake_envToBool_x3f___closed__10 = _init_l_Lake_envToBool_x3f___closed__10();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__10);
l_Lake_envToBool_x3f___closed__11 = _init_l_Lake_envToBool_x3f___closed__11();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__11);
l_Lake_envToBool_x3f___closed__12 = _init_l_Lake_envToBool_x3f___closed__12();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__12);
l_Lake_envToBool_x3f___closed__13 = _init_l_Lake_envToBool_x3f___closed__13();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__13);
l_Lake_envToBool_x3f___closed__14 = _init_l_Lake_envToBool_x3f___closed__14();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__14);
l_Lake_envToBool_x3f___closed__15 = _init_l_Lake_envToBool_x3f___closed__15();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__15);
l_Lake_envToBool_x3f___closed__16 = _init_l_Lake_envToBool_x3f___closed__16();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__16);
l_Lake_envToBool_x3f___closed__17 = _init_l_Lake_envToBool_x3f___closed__17();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__17);
l_Lake_envToBool_x3f___closed__18 = _init_l_Lake_envToBool_x3f___closed__18();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__18);
l_Lake_envToBool_x3f___closed__19 = _init_l_Lake_envToBool_x3f___closed__19();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__19);
l_Lake_envToBool_x3f___closed__20 = _init_l_Lake_envToBool_x3f___closed__20();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__20);
l_Lake_envToBool_x3f___closed__21 = _init_l_Lake_envToBool_x3f___closed__21();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__21);
l_Lake_envToBool_x3f___closed__22 = _init_l_Lake_envToBool_x3f___closed__22();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__22);
l_Lake_envToBool_x3f___closed__23 = _init_l_Lake_envToBool_x3f___closed__23();
lean_mark_persistent(l_Lake_envToBool_x3f___closed__23);
l_Lake_instInhabitedElanInstall_default___closed__0 = _init_l_Lake_instInhabitedElanInstall_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedElanInstall_default___closed__0);
l_Lake_instInhabitedElanInstall_default = _init_l_Lake_instInhabitedElanInstall_default();
lean_mark_persistent(l_Lake_instInhabitedElanInstall_default);
l_Lake_instInhabitedElanInstall = _init_l_Lake_instInhabitedElanInstall();
lean_mark_persistent(l_Lake_instInhabitedElanInstall);
l_Lake_instReprElanInstall_repr___redArg___closed__0 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__0();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__0);
l_Lake_instReprElanInstall_repr___redArg___closed__1 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__1();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__1);
l_Lake_instReprElanInstall_repr___redArg___closed__2 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__2();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__2);
l_Lake_instReprElanInstall_repr___redArg___closed__3 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__3();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__3);
l_Lake_instReprElanInstall_repr___redArg___closed__4 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__4();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__4);
l_Lake_instReprElanInstall_repr___redArg___closed__5 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__5();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__5);
l_Lake_instReprElanInstall_repr___redArg___closed__6 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__6();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__6);
l_Lake_instReprElanInstall_repr___redArg___closed__7 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__7();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__7);
l_Lake_instReprElanInstall_repr___redArg___closed__8 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__8();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__8);
l_Lake_instReprElanInstall_repr___redArg___closed__9 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__9();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__9);
l_Lake_instReprElanInstall_repr___redArg___closed__10 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__10();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__10);
l_Lake_instReprElanInstall_repr___redArg___closed__11 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__11();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__11);
l_Lake_instReprElanInstall_repr___redArg___closed__12 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__12();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__12);
l_Lake_instReprElanInstall_repr___redArg___closed__13 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__13();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__13);
l_Lake_instReprElanInstall_repr___redArg___closed__14 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__14();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__14);
l_Lake_instReprElanInstall_repr___redArg___closed__15 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__15();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__15);
l_Lake_instReprElanInstall_repr___redArg___closed__16 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__16();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__16);
l_Lake_instReprElanInstall_repr___redArg___closed__17 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__17();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__17);
l_Lake_instReprElanInstall_repr___redArg___closed__18 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__18();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__18);
l_Lake_instReprElanInstall_repr___redArg___closed__19 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__19();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__19);
l_Lake_instReprElanInstall_repr___redArg___closed__20 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__20();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__20);
l_Lake_instReprElanInstall_repr___redArg___closed__21 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__21();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__21);
l_Lake_instReprElanInstall_repr___redArg___closed__22 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__22();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__22);
l_Lake_instReprElanInstall_repr___redArg___closed__23 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__23();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__23);
l_Lake_instReprElanInstall_repr___redArg___closed__24 = _init_l_Lake_instReprElanInstall_repr___redArg___closed__24();
lean_mark_persistent(l_Lake_instReprElanInstall_repr___redArg___closed__24);
l_Lake_instReprElanInstall___closed__0 = _init_l_Lake_instReprElanInstall___closed__0();
lean_mark_persistent(l_Lake_instReprElanInstall___closed__0);
l_Lake_instReprElanInstall = _init_l_Lake_instReprElanInstall();
lean_mark_persistent(l_Lake_instReprElanInstall);
l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0 = _init_l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0);
l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1 = _init_l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1);
l_Lake_toolchain2Dir___closed__0 = _init_l_Lake_toolchain2Dir___closed__0();
lean_mark_persistent(l_Lake_toolchain2Dir___closed__0);
l_Lake_leanExe___closed__0 = _init_l_Lake_leanExe___closed__0();
lean_mark_persistent(l_Lake_leanExe___closed__0);
l_Lake_leanExe___closed__1 = _init_l_Lake_leanExe___closed__1();
lean_mark_persistent(l_Lake_leanExe___closed__1);
l_Lake_leancExe___closed__0 = _init_l_Lake_leancExe___closed__0();
lean_mark_persistent(l_Lake_leancExe___closed__0);
l_Lake_leanArExe___closed__0 = _init_l_Lake_leanArExe___closed__0();
lean_mark_persistent(l_Lake_leanArExe___closed__0);
l_Lake_leanCcExe___closed__0 = _init_l_Lake_leanCcExe___closed__0();
lean_mark_persistent(l_Lake_leanCcExe___closed__0);
l_Lake_leanSharedLibDir___closed__0 = _init_l_Lake_leanSharedLibDir___closed__0();
lean_mark_persistent(l_Lake_leanSharedLibDir___closed__0);
l_Lake_leanSharedLib___closed__0 = _init_l_Lake_leanSharedLib___closed__0();
lean_mark_persistent(l_Lake_leanSharedLib___closed__0);
l_Lake_leanSharedLib___closed__1 = _init_l_Lake_leanSharedLib___closed__1();
lean_mark_persistent(l_Lake_leanSharedLib___closed__1);
l_Lake_leanSharedLib = _init_l_Lake_leanSharedLib();
lean_mark_persistent(l_Lake_leanSharedLib);
l_Lake_initSharedLib___closed__0 = _init_l_Lake_initSharedLib___closed__0();
lean_mark_persistent(l_Lake_initSharedLib___closed__0);
l_Lake_initSharedLib___closed__1 = _init_l_Lake_initSharedLib___closed__1();
lean_mark_persistent(l_Lake_initSharedLib___closed__1);
l_Lake_initSharedLib = _init_l_Lake_initSharedLib();
lean_mark_persistent(l_Lake_initSharedLib);
l_Lake_instInhabitedLeanInstall_default___closed__0 = _init_l_Lake_instInhabitedLeanInstall_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default___closed__0);
l_Lake_instInhabitedLeanInstall_default___closed__1 = _init_l_Lake_instInhabitedLeanInstall_default___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default___closed__1);
l_Lake_instInhabitedLeanInstall_default = _init_l_Lake_instInhabitedLeanInstall_default();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default);
l_Lake_instInhabitedLeanInstall = _init_l_Lake_instInhabitedLeanInstall();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7);
l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8 = _init_l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8);
l_Lake_instReprLeanInstall_repr___redArg___closed__0 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__0();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__0);
l_Lake_instReprLeanInstall_repr___redArg___closed__1 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__1();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__1);
l_Lake_instReprLeanInstall_repr___redArg___closed__2 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__2();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__2);
l_Lake_instReprLeanInstall_repr___redArg___closed__3 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__3();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__3);
l_Lake_instReprLeanInstall_repr___redArg___closed__4 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__4);
l_Lake_instReprLeanInstall_repr___redArg___closed__5 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__5();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__5);
l_Lake_instReprLeanInstall_repr___redArg___closed__6 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__6();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__6);
l_Lake_instReprLeanInstall_repr___redArg___closed__7 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__7();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__7);
l_Lake_instReprLeanInstall_repr___redArg___closed__8 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__8();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__8);
l_Lake_instReprLeanInstall_repr___redArg___closed__9 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__9();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__9);
l_Lake_instReprLeanInstall_repr___redArg___closed__10 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__10();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__10);
l_Lake_instReprLeanInstall_repr___redArg___closed__11 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__11);
l_Lake_instReprLeanInstall_repr___redArg___closed__12 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__12();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__12);
l_Lake_instReprLeanInstall_repr___redArg___closed__13 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__13();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__13);
l_Lake_instReprLeanInstall_repr___redArg___closed__14 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__14();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__14);
l_Lake_instReprLeanInstall_repr___redArg___closed__15 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__15();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__15);
l_Lake_instReprLeanInstall_repr___redArg___closed__16 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__16);
l_Lake_instReprLeanInstall_repr___redArg___closed__17 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__17();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__17);
l_Lake_instReprLeanInstall_repr___redArg___closed__18 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__18();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__18);
l_Lake_instReprLeanInstall_repr___redArg___closed__19 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__19();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__19);
l_Lake_instReprLeanInstall_repr___redArg___closed__20 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__20);
l_Lake_instReprLeanInstall_repr___redArg___closed__21 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__21();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__21);
l_Lake_instReprLeanInstall_repr___redArg___closed__22 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__22();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__22);
l_Lake_instReprLeanInstall_repr___redArg___closed__23 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__23();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__23);
l_Lake_instReprLeanInstall_repr___redArg___closed__24 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__24);
l_Lake_instReprLeanInstall_repr___redArg___closed__25 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__25();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__25);
l_Lake_instReprLeanInstall_repr___redArg___closed__26 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__26();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__26);
l_Lake_instReprLeanInstall_repr___redArg___closed__27 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__27);
l_Lake_instReprLeanInstall_repr___redArg___closed__28 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__28);
l_Lake_instReprLeanInstall_repr___redArg___closed__29 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__29();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__29);
l_Lake_instReprLeanInstall_repr___redArg___closed__30 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__30();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__30);
l_Lake_instReprLeanInstall_repr___redArg___closed__31 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__31);
l_Lake_instReprLeanInstall_repr___redArg___closed__32 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__32);
l_Lake_instReprLeanInstall_repr___redArg___closed__33 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__33();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__33);
l_Lake_instReprLeanInstall_repr___redArg___closed__34 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__34();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__34);
l_Lake_instReprLeanInstall_repr___redArg___closed__35 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__35();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__35);
l_Lake_instReprLeanInstall_repr___redArg___closed__36 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__36);
l_Lake_instReprLeanInstall_repr___redArg___closed__37 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__37);
l_Lake_instReprLeanInstall_repr___redArg___closed__38 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__38();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__38);
l_Lake_instReprLeanInstall_repr___redArg___closed__39 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__39();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__39);
l_Lake_instReprLeanInstall_repr___redArg___closed__40 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__40();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__40);
l_Lake_instReprLeanInstall_repr___redArg___closed__41 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__41();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__41);
l_Lake_instReprLeanInstall_repr___redArg___closed__42 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__42();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__42);
l_Lake_instReprLeanInstall_repr___redArg___closed__43 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__43);
l_Lake_instReprLeanInstall_repr___redArg___closed__44 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__44);
l_Lake_instReprLeanInstall_repr___redArg___closed__45 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__45();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__45);
l_Lake_instReprLeanInstall_repr___redArg___closed__46 = _init_l_Lake_instReprLeanInstall_repr___redArg___closed__46();
lean_mark_persistent(l_Lake_instReprLeanInstall_repr___redArg___closed__46);
l_Lake_instReprLeanInstall___closed__0 = _init_l_Lake_instReprLeanInstall___closed__0();
lean_mark_persistent(l_Lake_instReprLeanInstall___closed__0);
l_Lake_instReprLeanInstall = _init_l_Lake_instReprLeanInstall();
lean_mark_persistent(l_Lake_instReprLeanInstall);
l_Lake_lakeExe___closed__0 = _init_l_Lake_lakeExe___closed__0();
lean_mark_persistent(l_Lake_lakeExe___closed__0);
l_Lake_lakeExe___closed__1 = _init_l_Lake_lakeExe___closed__1();
lean_mark_persistent(l_Lake_lakeExe___closed__1);
l_Lake_lakeExe = _init_l_Lake_lakeExe();
lean_mark_persistent(l_Lake_lakeExe);
l_Lake_instInhabitedLakeInstall_default___closed__0 = _init_l_Lake_instInhabitedLakeInstall_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall_default___closed__0);
l_Lake_instInhabitedLakeInstall_default = _init_l_Lake_instInhabitedLakeInstall_default();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall_default);
l_Lake_instInhabitedLakeInstall = _init_l_Lake_instInhabitedLakeInstall();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall);
l_Lake_instReprLakeInstall_repr___redArg___closed__0 = _init_l_Lake_instReprLakeInstall_repr___redArg___closed__0();
lean_mark_persistent(l_Lake_instReprLakeInstall_repr___redArg___closed__0);
l_Lake_instReprLakeInstall_repr___redArg___closed__1 = _init_l_Lake_instReprLakeInstall_repr___redArg___closed__1();
lean_mark_persistent(l_Lake_instReprLakeInstall_repr___redArg___closed__1);
l_Lake_instReprLakeInstall_repr___redArg___closed__2 = _init_l_Lake_instReprLakeInstall_repr___redArg___closed__2();
lean_mark_persistent(l_Lake_instReprLakeInstall_repr___redArg___closed__2);
l_Lake_instReprLakeInstall_repr___redArg___closed__3 = _init_l_Lake_instReprLakeInstall_repr___redArg___closed__3();
lean_mark_persistent(l_Lake_instReprLakeInstall_repr___redArg___closed__3);
l_Lake_instReprLakeInstall_repr___redArg___closed__4 = _init_l_Lake_instReprLakeInstall_repr___redArg___closed__4();
lean_mark_persistent(l_Lake_instReprLakeInstall_repr___redArg___closed__4);
l_Lake_instReprLakeInstall___closed__0 = _init_l_Lake_instReprLakeInstall___closed__0();
lean_mark_persistent(l_Lake_instReprLakeInstall___closed__0);
l_Lake_instReprLakeInstall = _init_l_Lake_instReprLakeInstall();
lean_mark_persistent(l_Lake_instReprLakeInstall);
l_Lake_LakeInstall_ofLean___closed__0 = _init_l_Lake_LakeInstall_ofLean___closed__0();
lean_mark_persistent(l_Lake_LakeInstall_ofLean___closed__0);
l_Lake_LakeInstall_ofLean___closed__1 = _init_l_Lake_LakeInstall_ofLean___closed__1();
lean_mark_persistent(l_Lake_LakeInstall_ofLean___closed__1);
l_Lake_LakeInstall_ofLean___closed__2 = _init_l_Lake_LakeInstall_ofLean___closed__2();
lean_mark_persistent(l_Lake_LakeInstall_ofLean___closed__2);
l_Lake_LakeInstall_ofLean___closed__3 = _init_l_Lake_LakeInstall_ofLean___closed__3();
lean_mark_persistent(l_Lake_LakeInstall_ofLean___closed__3);
l_Lake_findElanInstall_x3f___closed__0 = _init_l_Lake_findElanInstall_x3f___closed__0();
lean_mark_persistent(l_Lake_findElanInstall_x3f___closed__0);
l_Lake_findElanInstall_x3f___closed__1 = _init_l_Lake_findElanInstall_x3f___closed__1();
lean_mark_persistent(l_Lake_findElanInstall_x3f___closed__1);
l_Lake_findElanInstall_x3f___closed__2 = _init_l_Lake_findElanInstall_x3f___closed__2();
lean_mark_persistent(l_Lake_findElanInstall_x3f___closed__2);
l_Lake_findLeanSysroot_x3f___closed__0 = _init_l_Lake_findLeanSysroot_x3f___closed__0();
lean_mark_persistent(l_Lake_findLeanSysroot_x3f___closed__0);
l_Lake_findLeanSysroot_x3f___closed__1 = _init_l_Lake_findLeanSysroot_x3f___closed__1();
lean_mark_persistent(l_Lake_findLeanSysroot_x3f___closed__1);
l_Lake_findLeanSysroot_x3f___closed__2 = _init_l_Lake_findLeanSysroot_x3f___closed__2();
lean_mark_persistent(l_Lake_findLeanSysroot_x3f___closed__2);
l_Lake_findLeanSysroot_x3f___closed__3 = _init_l_Lake_findLeanSysroot_x3f___closed__3();
lean_mark_persistent(l_Lake_findLeanSysroot_x3f___closed__3);
l_Lake_findLeanSysroot_x3f___closed__4 = _init_l_Lake_findLeanSysroot_x3f___closed__4();
lean_mark_persistent(l_Lake_findLeanSysroot_x3f___closed__4);
l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0 = _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0);
l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1 = _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1);
l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0 = _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0);
l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1 = _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1);
l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0 = _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0);
l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1 = _init_l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1();
lean_mark_persistent(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1);
l_Lake_LeanInstall_get___closed__0 = _init_l_Lake_LeanInstall_get___closed__0();
lean_mark_persistent(l_Lake_LeanInstall_get___closed__0);
l_Lake_LeanInstall_get___closed__1 = _init_l_Lake_LeanInstall_get___closed__1();
lean_mark_persistent(l_Lake_LeanInstall_get___closed__1);
l_Lake_LeanInstall_get___closed__2 = _init_l_Lake_LeanInstall_get___closed__2();
lean_mark_persistent(l_Lake_LeanInstall_get___closed__2);
l_Lake_LeanInstall_get___closed__3 = _init_l_Lake_LeanInstall_get___closed__3();
lean_mark_persistent(l_Lake_LeanInstall_get___closed__3);
l_Lake_LeanInstall_get___closed__4 = _init_l_Lake_LeanInstall_get___closed__4();
lean_mark_persistent(l_Lake_LeanInstall_get___closed__4);
l_Lake_LeanInstall_get___closed__5 = _init_l_Lake_LeanInstall_get___closed__5();
lean_mark_persistent(l_Lake_LeanInstall_get___closed__5);
l_Lake_getLakeInstall_x3f___closed__0 = _init_l_Lake_getLakeInstall_x3f___closed__0();
lean_mark_persistent(l_Lake_getLakeInstall_x3f___closed__0);
l_Lake_getLakeInstall_x3f___closed__1 = _init_l_Lake_getLakeInstall_x3f___closed__1();
lean_mark_persistent(l_Lake_getLakeInstall_x3f___closed__1);
l_Lake_getLakeInstall_x3f___closed__2 = _init_l_Lake_getLakeInstall_x3f___closed__2();
lean_mark_persistent(l_Lake_getLakeInstall_x3f___closed__2);
l_Lake_findLeanInstall_x3f___closed__0 = _init_l_Lake_findLeanInstall_x3f___closed__0();
lean_mark_persistent(l_Lake_findLeanInstall_x3f___closed__0);
l_Lake_findLeanInstall_x3f___closed__1 = _init_l_Lake_findLeanInstall_x3f___closed__1();
lean_mark_persistent(l_Lake_findLeanInstall_x3f___closed__1);
l_Lake_findLakeInstall_x3f___closed__0 = _init_l_Lake_findLakeInstall_x3f___closed__0();
lean_mark_persistent(l_Lake_findLakeInstall_x3f___closed__0);
l_Lake_findInstall_x3f___closed__0 = _init_l_Lake_findInstall_x3f___closed__0();
lean_mark_persistent(l_Lake_findInstall_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
