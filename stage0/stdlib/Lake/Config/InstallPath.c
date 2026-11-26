// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: public import Lean.Compiler.FFI public import Lake.Config.Dynlib public import Lake.Config.Defaults public import Lake.Util.NativeLib import Init.Data.UInt.Lemmas import Init.Data.String.Modify import Init.System.Platform
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
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
extern lean_object* l_Lake_defaultLeanLibDir;
extern lean_object* l_Lake_defaultBuildDir;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_app_path();
lean_object* l_System_FilePath_parent(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern uint8_t l_System_Platform_isWindows;
extern lean_object* l_Lake_sharedLibExt;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBinDir;
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lake_envToBool_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l_Lake_envToBool_x3f___closed__0 = (const lean_object*)&l_Lake_envToBool_x3f___closed__0_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "yes"};
static const lean_object* l_Lake_envToBool_x3f___closed__1 = (const lean_object*)&l_Lake_envToBool_x3f___closed__1_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lake_envToBool_x3f___closed__2 = (const lean_object*)&l_Lake_envToBool_x3f___closed__2_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_envToBool_x3f___closed__3 = (const lean_object*)&l_Lake_envToBool_x3f___closed__3_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "on"};
static const lean_object* l_Lake_envToBool_x3f___closed__4 = (const lean_object*)&l_Lake_envToBool_x3f___closed__4_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Lake_envToBool_x3f___closed__5 = (const lean_object*)&l_Lake_envToBool_x3f___closed__5_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_envToBool_x3f___closed__6 = (const lean_object*)&l_Lake_envToBool_x3f___closed__6_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__4_value),((lean_object*)&l_Lake_envToBool_x3f___closed__6_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__7 = (const lean_object*)&l_Lake_envToBool_x3f___closed__7_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__3_value),((lean_object*)&l_Lake_envToBool_x3f___closed__7_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__8 = (const lean_object*)&l_Lake_envToBool_x3f___closed__8_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__2_value),((lean_object*)&l_Lake_envToBool_x3f___closed__8_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__9 = (const lean_object*)&l_Lake_envToBool_x3f___closed__9_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__1_value),((lean_object*)&l_Lake_envToBool_x3f___closed__9_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__10 = (const lean_object*)&l_Lake_envToBool_x3f___closed__10_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__0_value),((lean_object*)&l_Lake_envToBool_x3f___closed__10_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__11 = (const lean_object*)&l_Lake_envToBool_x3f___closed__11_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Lake_envToBool_x3f___closed__12 = (const lean_object*)&l_Lake_envToBool_x3f___closed__12_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "no"};
static const lean_object* l_Lake_envToBool_x3f___closed__13 = (const lean_object*)&l_Lake_envToBool_x3f___closed__13_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lake_envToBool_x3f___closed__14 = (const lean_object*)&l_Lake_envToBool_x3f___closed__14_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_envToBool_x3f___closed__15 = (const lean_object*)&l_Lake_envToBool_x3f___closed__15_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "off"};
static const lean_object* l_Lake_envToBool_x3f___closed__16 = (const lean_object*)&l_Lake_envToBool_x3f___closed__16_value;
static const lean_string_object l_Lake_envToBool_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Lake_envToBool_x3f___closed__17 = (const lean_object*)&l_Lake_envToBool_x3f___closed__17_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_envToBool_x3f___closed__18 = (const lean_object*)&l_Lake_envToBool_x3f___closed__18_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__16_value),((lean_object*)&l_Lake_envToBool_x3f___closed__18_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__19 = (const lean_object*)&l_Lake_envToBool_x3f___closed__19_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__15_value),((lean_object*)&l_Lake_envToBool_x3f___closed__19_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__20 = (const lean_object*)&l_Lake_envToBool_x3f___closed__20_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__14_value),((lean_object*)&l_Lake_envToBool_x3f___closed__20_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__21 = (const lean_object*)&l_Lake_envToBool_x3f___closed__21_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__13_value),((lean_object*)&l_Lake_envToBool_x3f___closed__21_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__22 = (const lean_object*)&l_Lake_envToBool_x3f___closed__22_value;
static const lean_ctor_object l_Lake_envToBool_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_envToBool_x3f___closed__12_value),((lean_object*)&l_Lake_envToBool_x3f___closed__22_value)}};
static const lean_object* l_Lake_envToBool_x3f___closed__23 = (const lean_object*)&l_Lake_envToBool_x3f___closed__23_value;
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object*);
static const lean_string_object l_Lake_instInhabitedElanInstall_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedElanInstall_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedElanInstall_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lake_instInhabitedElanInstall_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedElanInstall_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedElanInstall_default___closed__2;
static const lean_string_object l_Lake_instInhabitedElanInstall_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toolchains"};
static const lean_object* l_Lake_instInhabitedElanInstall_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedElanInstall_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedElanInstall_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedElanInstall_default___closed__4;
static lean_once_cell_t l_Lake_instInhabitedElanInstall_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedElanInstall_default___closed__5;
LEAN_EXPORT lean_object* l_Lake_instInhabitedElanInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedElanInstall;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "home"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__11_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elan"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binDir"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__15 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__16;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toolchainsDir"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__17_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__19;
static const lean_string_object l_Lake_instReprElanInstall_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__20 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__21;
static lean_once_cell_t l_Lake_instReprElanInstall_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__22;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__23 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lake_instReprElanInstall_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__20_value)}};
static const lean_object* l_Lake_instReprElanInstall_repr___redArg___closed__24 = (const lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__24_value;
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprElanInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprElanInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprElanInstall___closed__0 = (const lean_object*)&l_Lake_instReprElanInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprElanInstall = (const lean_object*)&l_Lake_instReprElanInstall___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "---"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_leanExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_leanExe___closed__0 = (const lean_object*)&l_Lake_leanExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object*);
static const lean_string_object l_Lake_leanirExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "leanir"};
static const lean_object* l_Lake_leanirExe___closed__0 = (const lean_object*)&l_Lake_leanirExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object*);
static const lean_string_object l_Lake_leancExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "leanc"};
static const lean_object* l_Lake_leancExe___closed__0 = (const lean_object*)&l_Lake_leancExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object*);
static const lean_string_object l_Lake_leantarExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leantar"};
static const lean_object* l_Lake_leantarExe___closed__0 = (const lean_object*)&l_Lake_leantarExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object*);
static const lean_string_object l_Lake_leanArExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "llvm-ar"};
static const lean_object* l_Lake_leanArExe___closed__0 = (const lean_object*)&l_Lake_leanArExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object*);
static const lean_string_object l_Lake_leanCcExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clang"};
static const lean_object* l_Lake_leanCcExe___closed__0 = (const lean_object*)&l_Lake_leanCcExe___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object*);
static const lean_string_object l_Lake_leanSharedLibDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_leanSharedLibDir___closed__0 = (const lean_object*)&l_Lake_leanSharedLibDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".dll"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0_value;
static const lean_array_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Init_shared"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "leanshared_1"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "leanshared_2"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "leanshared_3"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanshared"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__4 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs(lean_object*);
static const lean_string_object l_Lake_leanSharedDynlibs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libInit_shared."};
static const lean_object* l_Lake_leanSharedDynlibs___closed__0 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__0_value;
static lean_once_cell_t l_Lake_leanSharedDynlibs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedDynlibs___closed__1;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libleanshared_1."};
static const lean_object* l_Lake_leanSharedDynlibs___closed__2 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__2_value;
static lean_once_cell_t l_Lake_leanSharedDynlibs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedDynlibs___closed__3;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libleanshared_2."};
static const lean_object* l_Lake_leanSharedDynlibs___closed__4 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__4_value;
static lean_once_cell_t l_Lake_leanSharedDynlibs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedDynlibs___closed__5;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libleanshared_3."};
static const lean_object* l_Lake_leanSharedDynlibs___closed__6 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__6_value;
static lean_once_cell_t l_Lake_leanSharedDynlibs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedDynlibs___closed__7;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "libleanshared."};
static const lean_object* l_Lake_leanSharedDynlibs___closed__8 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__8_value;
static lean_once_cell_t l_Lake_leanSharedDynlibs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedDynlibs___closed__9;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libInit_shared.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__10 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__10_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "libleanshared_1.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__11 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__11_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "libleanshared_2.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__12 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__12_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "libleanshared_3.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__13 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__13_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "libleanshared.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__14 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__14_value;
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlib(lean_object*);
static const lean_string_object l_Lake_leanSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "libleanshared"};
static const lean_object* l_Lake_leanSharedLib___closed__0 = (const lean_object*)&l_Lake_leanSharedLib___closed__0_value;
static lean_once_cell_t l_Lake_leanSharedLib___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedLib___closed__1;
LEAN_EXPORT lean_object* l_Lake_leanSharedLib;
static const lean_string_object l_Lake_initSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "libInit_shared"};
static const lean_object* l_Lake_initSharedLib___closed__0 = (const lean_object*)&l_Lake_initSharedLib___closed__0_value;
static lean_once_cell_t l_Lake_initSharedLib___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initSharedLib___closed__1;
LEAN_EXPORT lean_object* l_Lake_initSharedLib;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__1;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__2;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__3;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__4;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__5 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__5_value;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__6;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__7;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__8;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__9;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__10;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__11;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__12;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ar"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__13 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__13_value;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "cc"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__14 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__14_value;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "-Wno-unused-command-line-argument"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__15 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__15_value;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__16;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__17;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__18;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__19;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sysroot"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "githash"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__6_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "srcDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__7 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__7_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__8_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanLibDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__9_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__11;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "includeDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "systemLibDir"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__15 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__16;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leanExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leanirExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leancExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__19 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__20;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leantarExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__21 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__21_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sharedDynlibs"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__22 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__23 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__23_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sharedDynlib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__24 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__24_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__24_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__25 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__13_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__26 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__26_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__27;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__14_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__28 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__28_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "customCc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__29 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__29_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__29_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__30 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__31;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__32 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__32_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__32_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__33 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__33_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__34 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__34_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__34_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__35 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__36;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__37 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__37_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__37_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__38 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__38_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ccFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__39 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__39_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__39_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__43;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__44 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__44_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__44_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__45_value;
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLeanInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLeanInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLeanInstall___closed__0 = (const lean_object*)&l_Lake_instReprLeanInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLeanInstall = (const lean_object*)&l_Lake_instReprLeanInstall___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_initSharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_lakeExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l_Lake_lakeExe___closed__0 = (const lean_object*)&l_Lake_lakeExe___closed__0_value;
static lean_once_cell_t l_Lake_lakeExe___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_lakeExe___closed__1;
LEAN_EXPORT lean_object* l_Lake_lakeExe;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__0;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__1;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__2;
static const lean_string_object l_Lake_instInhabitedLakeInstall_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instInhabitedLakeInstall_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedLakeInstall_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__4;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__5;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__6;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__7;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__8;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall;
static const lean_string_object l_Lake_instReprLakeInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "libDir"};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_lakeExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLakeInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLakeInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLakeInstall___closed__0 = (const lean_object*)&l_Lake_instReprLakeInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLakeInstall = (const lean_object*)&l_Lake_instReprLakeInstall___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object*);
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lake_shared"};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__0 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__0_value;
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libLake_shared."};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__1 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__1_value;
static lean_once_cell_t l_Lake_LakeInstall_ofLean___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeInstall_ofLean___closed__2;
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libLake_shared.dll"};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__3 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object*);
static const lean_string_object l_Lake_findElanInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ELAN_HOME"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__0_value;
static const lean_string_object l_Lake_findElanInstall_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ELAN"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__1 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object*);
static const lean_ctor_object l_Lake_findLeanSysroot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__0 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__0_value;
static const lean_string_object l_Lake_findLeanSysroot_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "--print-prefix"};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__1 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__1_value;
static const lean_array_object l_Lake_findLeanSysroot_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_findLeanSysroot_x3f___closed__1_value)}};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__2 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__2_value;
static const lean_array_object l_Lake_findLeanSysroot_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_findLeanSysroot_x3f___closed__3 = (const lean_object*)&l_Lake_findLeanSysroot_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--githash"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value;
static const lean_array_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value)}};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_AR"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AR"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "LEAN_CC"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value;
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "CC"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f();
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object*);
static const lean_string_object l_Lake_getLakeInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lake.olean"};
static const lean_object* l_Lake_getLakeInstall_x3f___closed__0 = (const lean_object*)&l_Lake_getLakeInstall_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_findLeanInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_SYSROOT"};
static const lean_object* l_Lake_findLeanInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findLeanInstall_x3f___closed__0_value;
static const lean_string_object l_Lake_findLeanInstall_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LEAN"};
static const lean_object* l_Lake_findLeanInstall_x3f___closed__1 = (const lean_object*)&l_Lake_findLeanInstall_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_findLakeInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LAKE_HOME"};
static const lean_object* l_Lake_findLakeInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findLakeInstall_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_findInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LAKE_OVERRIDE_LEAN"};
static const lean_object* l_Lake_findInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findInstall_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f();
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v___x_6_ = lean_string_dec_eq(v_a_1_, v_head_4_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object* v_s_12_, lean_object* v_p_13_){
_start:
{
lean_object* v___y_15_; lean_object* v___y_16_; uint32_t v___y_20_; lean_object* v___x_32_; uint8_t v_decide_33_; 
v___x_32_ = lean_string_utf8_byte_size(v_s_12_);
v_decide_33_ = lean_nat_dec_eq(v_p_13_, v___x_32_);
if (v_decide_33_ == 0)
{
uint32_t v___x_34_; uint32_t v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_string_utf8_get_fast(v_s_12_, v_p_13_);
v___x_35_ = 65;
v___x_36_ = lean_uint32_dec_le(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
v___y_20_ = v___x_34_;
goto v___jp_19_;
}
else
{
uint32_t v___x_37_; uint8_t v___x_38_; 
v___x_37_ = 90;
v___x_38_ = lean_uint32_dec_le(v___x_34_, v___x_37_);
if (v___x_38_ == 0)
{
v___y_20_ = v___x_34_;
goto v___jp_19_;
}
else
{
uint32_t v___x_39_; uint32_t v___x_40_; 
v___x_39_ = 32;
v___x_40_ = lean_uint32_add(v___x_34_, v___x_39_);
v___y_20_ = v___x_40_;
goto v___jp_19_;
}
}
}
else
{
lean_dec(v_p_13_);
return v_s_12_;
}
v___jp_14_:
{
lean_object* v___x_17_; 
v___x_17_ = lean_nat_add(v_p_13_, v___y_16_);
lean_dec(v_p_13_);
v_s_12_ = v___y_15_;
v_p_13_ = v___x_17_;
goto _start;
}
v___jp_19_:
{
lean_object* v___x_21_; uint32_t v___x_22_; uint8_t v___x_23_; 
lean_inc(v_p_13_);
v___x_21_ = lean_string_utf8_set(v_s_12_, v_p_13_, v___y_20_);
v___x_22_ = 127;
v___x_23_ = lean_uint32_dec_le(v___y_20_, v___x_22_);
if (v___x_23_ == 0)
{
uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 2047;
v___x_25_ = lean_uint32_dec_le(v___y_20_, v___x_24_);
if (v___x_25_ == 0)
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 65535;
v___x_27_ = lean_uint32_dec_le(v___y_20_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_unsigned_to_nat(4u);
v___y_15_ = v___x_21_;
v___y_16_ = v___x_28_;
goto v___jp_14_;
}
else
{
lean_object* v___x_29_; 
v___x_29_ = lean_unsigned_to_nat(3u);
v___y_15_ = v___x_21_;
v___y_16_ = v___x_29_;
goto v___jp_14_;
}
}
else
{
lean_object* v___x_30_; 
v___x_30_ = lean_unsigned_to_nat(2u);
v___y_15_ = v___x_21_;
v___y_16_ = v___x_30_;
goto v___jp_14_;
}
}
else
{
lean_object* v___x_31_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___y_15_ = v___x_21_;
v___y_16_ = v___x_31_;
goto v___jp_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* v_o_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_90_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__11));
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_89_, v___x_91_);
v___x_93_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_92_, v___x_90_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__23));
v___x_95_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_92_, v___x_94_);
lean_dec_ref(v___x_92_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_box(v___x_93_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec_ref(v___x_92_);
v___x_99_ = lean_box(v___x_93_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_104_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_105_ = l_System_FilePath_join(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_108_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_109_ = l_System_FilePath_join(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__5(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__4, &l_Lake_instInhabitedElanInstall_default___closed__4_once, _init_l_Lake_instInhabitedElanInstall_default___closed__4);
v___x_111_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_112_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
lean_ctor_set(v___x_113_, 2, v___x_111_);
lean_ctor_set(v___x_113_, 3, v___x_110_);
return v___x_113_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__5, &l_Lake_instInhabitedElanInstall_default___closed__5_once, _init_l_Lake_instInhabitedElanInstall_default___closed__5);
return v___x_114_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lake_instInhabitedElanInstall_default;
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* v_a_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_nat_to_int(v_a_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(8u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(10u);
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(17u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__0));
v___x_154_ = lean_string_length(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__21, &l_Lake_instReprElanInstall_repr___redArg___closed__21_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__21);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* v_x_161_){
_start:
{
lean_object* v_home_162_; lean_object* v_elan_163_; lean_object* v_binDir_164_; lean_object* v_toolchainsDir_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_home_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_home_162_);
v_elan_163_ = lean_ctor_get(v_x_161_, 1);
lean_inc_ref(v_elan_163_);
v_binDir_164_ = lean_ctor_get(v_x_161_, 2);
lean_inc_ref(v_binDir_164_);
v_toolchainsDir_165_ = lean_ctor_get(v_x_161_, 3);
lean_inc_ref(v_toolchainsDir_165_);
lean_dec_ref(v_x_161_);
v___x_166_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_167_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_168_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_171_ = l_String_quote(v_home_162_);
v___x_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Repr_addAppParen(v___x_173_, v___x_169_);
v___x_175_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_168_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = 0;
v___x_177_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*1, v___x_176_);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_167_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_box(1);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__13));
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_166_);
v___x_186_ = l_String_quote(v_elan_163_);
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_170_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Repr_addAppParen(v___x_188_, v___x_169_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_168_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_176_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_185_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_179_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_181_);
v___x_195_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_166_);
v___x_198_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_199_ = l_String_quote(v_binDir_164_);
v___x_200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_170_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Repr_addAppParen(v___x_201_, v___x_169_);
v___x_203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_198_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*1, v___x_176_);
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_197_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_179_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_181_);
v___x_208_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__18));
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_166_);
v___x_211_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_212_ = l_String_quote(v_toolchainsDir_165_);
v___x_213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_170_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = l_Repr_addAppParen(v___x_214_, v___x_169_);
v___x_216_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_211_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*1, v___x_176_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_210_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_220_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_218_);
v___x_222_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_176_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* v_x_226_, lean_object* v_prec_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lake_instReprElanInstall_repr___redArg(v_x_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* v_x_229_, lean_object* v_prec_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_instReprElanInstall_repr(v_x_229_, v_prec_230_);
lean_dec(v_prec_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* v_toolchain_236_, lean_object* v_acc_237_, lean_object* v_pos_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_string_utf8_at_end(v_toolchain_236_, v_pos_238_);
if (v___x_239_ == 0)
{
uint32_t v_c_240_; lean_object* v_pos_x27_241_; uint32_t v___x_242_; uint8_t v___x_243_; 
v_c_240_ = lean_string_utf8_get_fast(v_toolchain_236_, v_pos_238_);
v_pos_x27_241_ = lean_string_utf8_next_fast(v_toolchain_236_, v_pos_238_);
lean_dec(v_pos_238_);
v___x_242_ = 47;
v___x_243_ = lean_uint32_dec_eq(v_c_240_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 58;
v___x_245_ = lean_uint32_dec_eq(v_c_240_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_string_push(v_acc_237_, v_c_240_);
v_acc_237_ = v___x_246_;
v_pos_238_ = v_pos_x27_241_;
goto _start;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0));
v___x_249_ = lean_string_append(v_acc_237_, v___x_248_);
v_acc_237_ = v___x_249_;
v_pos_238_ = v_pos_x27_241_;
goto _start;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1));
v___x_252_ = lean_string_append(v_acc_237_, v___x_251_);
v_acc_237_ = v___x_252_;
v_pos_238_ = v_pos_x27_241_;
goto _start;
}
}
else
{
lean_dec(v_pos_238_);
return v_acc_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* v_toolchain_254_, lean_object* v_acc_255_, lean_object* v_pos_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_254_, v_acc_255_, v_pos_256_);
lean_dec_ref(v_toolchain_254_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* v_toolchain_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_258_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* v_toolchain_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lake_toolchain2Dir(v_toolchain_262_);
lean_dec_ref(v_toolchain_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* v_toolchain_264_, lean_object* v_elan_265_){
_start:
{
lean_object* v_toolchainsDir_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_toolchainsDir_266_ = lean_ctor_get(v_elan_265_, 3);
lean_inc_ref(v_toolchainsDir_266_);
lean_dec_ref(v_elan_265_);
v___x_267_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_264_, v___x_267_, v___x_268_);
v___x_270_ = l_System_FilePath_join(v_toolchainsDir_266_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* v_toolchain_271_, lean_object* v_elan_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_271_, v_elan_272_);
lean_dec_ref(v_toolchain_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* v_sysroot_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_277_ = l_System_FilePath_join(v_sysroot_275_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_279_ = l_System_FilePath_join(v___x_277_, v___x_278_);
v___x_280_ = l_System_FilePath_exeExtension;
v___x_281_ = l_System_FilePath_addExtension(v___x_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object* v_sysroot_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_284_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_285_ = l_System_FilePath_join(v_sysroot_283_, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lake_leanirExe___closed__0));
v___x_287_ = l_System_FilePath_join(v___x_285_, v___x_286_);
v___x_288_ = l_System_FilePath_exeExtension;
v___x_289_ = l_System_FilePath_addExtension(v___x_287_, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_293_ = l_System_FilePath_join(v_sysroot_291_, v___x_292_);
v___x_294_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_295_ = l_System_FilePath_join(v___x_293_, v___x_294_);
v___x_296_ = l_System_FilePath_exeExtension;
v___x_297_ = l_System_FilePath_addExtension(v___x_295_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_300_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_301_ = l_System_FilePath_join(v_sysroot_299_, v___x_300_);
v___x_302_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_303_ = l_System_FilePath_join(v___x_301_, v___x_302_);
v___x_304_ = l_System_FilePath_exeExtension;
v___x_305_ = l_System_FilePath_addExtension(v___x_303_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_308_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_309_ = l_System_FilePath_join(v_sysroot_307_, v___x_308_);
v___x_310_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_311_ = l_System_FilePath_join(v___x_309_, v___x_310_);
v___x_312_ = l_System_FilePath_exeExtension;
v___x_313_ = l_System_FilePath_addExtension(v___x_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_316_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_317_ = l_System_FilePath_join(v_sysroot_315_, v___x_316_);
v___x_318_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_319_ = l_System_FilePath_join(v___x_317_, v___x_318_);
v___x_320_ = l_System_FilePath_exeExtension;
v___x_321_ = l_System_FilePath_addExtension(v___x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = l_System_Platform_isWindows;
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_326_ = l_System_FilePath_join(v_sysroot_323_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_328_ = l_System_FilePath_join(v___x_326_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_330_ = l_System_FilePath_join(v_sysroot_323_, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib(lean_object* v_sysroot_334_, lean_object* v_name_335_, lean_object* v_deps_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_337_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_338_ = l_System_FilePath_join(v_sysroot_334_, v___x_337_);
v___x_339_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_340_ = lean_string_append(v___x_339_, v_name_335_);
v___x_341_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0));
v___x_342_ = lean_string_append(v___x_340_, v___x_341_);
v___x_343_ = l_System_FilePath_join(v___x_338_, v___x_342_);
v___x_344_ = 0;
v___x_345_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_346_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_346_, 0, v___x_343_);
lean_ctor_set(v___x_346_, 1, v_name_335_);
lean_ctor_set(v___x_346_, 2, v_deps_336_);
lean_ctor_set(v___x_346_, 3, v___x_345_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*4, v___x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg(lean_object* v_sysroot_348_, lean_object* v_name_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_350_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_351_ = l_System_FilePath_join(v_sysroot_348_, v___x_350_);
v___x_352_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_353_ = l_System_FilePath_join(v___x_351_, v___x_352_);
v___x_354_ = lean_string_append(v___x_350_, v_name_349_);
v___x_355_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
v___x_357_ = l_Lake_sharedLibExt;
v___x_358_ = lean_string_append(v___x_356_, v___x_357_);
v___x_359_ = l_System_FilePath_join(v___x_353_, v___x_358_);
v___x_360_ = 0;
v___x_361_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_362_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v_name_349_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
lean_ctor_set(v___x_362_, 3, v___x_361_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*4, v___x_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(lean_object* v_sysroot_363_, lean_object* v_name_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_366_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_367_ = l_System_FilePath_join(v_sysroot_363_, v___x_366_);
v___x_368_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_369_ = l_System_FilePath_join(v___x_367_, v___x_368_);
v___x_370_ = lean_string_append(v___x_366_, v_name_364_);
v___x_371_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
v___x_373_ = l_Lake_sharedLibExt;
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
v___x_375_ = l_System_FilePath_join(v___x_369_, v___x_374_);
v___x_376_ = 0;
v___x_377_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_378_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_378_, 0, v___x_375_);
lean_ctor_set(v___x_378_, 1, v_name_364_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
lean_ctor_set(v___x_378_, 3, v___x_377_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*4, v___x_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___boxed(lean_object* v_sysroot_379_, lean_object* v_name_380_, lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(v_sysroot_379_, v_name_380_, v_x_381_);
lean_dec_ref(v_x_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs(lean_object* v_f_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_init_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_lean1_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_lean2_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_lean3_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_lean_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_389_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_390_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
lean_inc_ref_n(v_f_388_, 4);
v_init_391_ = lean_apply_2(v_f_388_, v___x_389_, v___x_390_);
v___x_392_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
lean_inc_ref_n(v_init_391_, 4);
v___x_395_ = lean_array_push(v___x_394_, v_init_391_);
v_lean1_396_ = lean_apply_2(v_f_388_, v___x_392_, v___x_395_);
v___x_397_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_398_ = lean_unsigned_to_nat(2u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
lean_inc_ref_n(v_lean1_396_, 3);
v___x_400_ = lean_array_push(v___x_399_, v_lean1_396_);
v___x_401_ = lean_array_push(v___x_400_, v_init_391_);
v_lean2_402_ = lean_apply_2(v_f_388_, v___x_397_, v___x_401_);
v___x_403_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_404_ = lean_unsigned_to_nat(3u);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
lean_inc_ref_n(v_lean2_402_, 2);
v___x_406_ = lean_array_push(v___x_405_, v_lean2_402_);
v___x_407_ = lean_array_push(v___x_406_, v_lean1_396_);
v___x_408_ = lean_array_push(v___x_407_, v_init_391_);
v_lean3_409_ = lean_apply_2(v_f_388_, v___x_403_, v___x_408_);
v___x_410_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__4));
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = lean_mk_empty_array_with_capacity(v___x_411_);
lean_inc_ref(v_lean3_409_);
v___x_413_ = lean_array_push(v___x_412_, v_lean3_409_);
v___x_414_ = lean_array_push(v___x_413_, v_lean2_402_);
v___x_415_ = lean_array_push(v___x_414_, v_lean1_396_);
v___x_416_ = lean_array_push(v___x_415_, v_init_391_);
v_lean_417_ = lean_apply_2(v_f_388_, v___x_410_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(5u);
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_418_);
v___x_420_ = lean_array_push(v___x_419_, v_lean_417_);
v___x_421_ = lean_array_push(v___x_420_, v_lean3_409_);
v___x_422_ = lean_array_push(v___x_421_, v_lean2_402_);
v___x_423_ = lean_array_push(v___x_422_, v_lean1_396_);
v___x_424_ = lean_array_push(v___x_423_, v_init_391_);
return v___x_424_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__1(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = l_Lake_sharedLibExt;
v___x_427_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__0));
v___x_428_ = lean_string_append(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__3(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = l_Lake_sharedLibExt;
v___x_431_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__2));
v___x_432_ = lean_string_append(v___x_431_, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__5(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lake_sharedLibExt;
v___x_435_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__4));
v___x_436_ = lean_string_append(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__7(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = l_Lake_sharedLibExt;
v___x_439_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__6));
v___x_440_ = lean_string_append(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__9(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = l_Lake_sharedLibExt;
v___x_443_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__8));
v___x_444_ = lean_string_append(v___x_443_, v___x_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlibs(lean_object* v_sysroot_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_System_Platform_isWindows;
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_init_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_lean1_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_lean2_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_lean3_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_lean_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_452_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_453_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_454_ = l_System_FilePath_join(v_sysroot_450_, v___x_453_);
v___x_455_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_456_ = l_System_FilePath_join(v___x_454_, v___x_455_);
v___x_457_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__1, &l_Lake_leanSharedDynlibs___closed__1_once, _init_l_Lake_leanSharedDynlibs___closed__1);
lean_inc_ref_n(v___x_456_, 4);
v___x_458_ = l_System_FilePath_join(v___x_456_, v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v_init_460_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_460_, 0, v___x_458_);
lean_ctor_set(v_init_460_, 1, v___x_452_);
lean_ctor_set(v_init_460_, 2, v___x_459_);
lean_ctor_set(v_init_460_, 3, v___x_459_);
lean_ctor_set_uint8(v_init_460_, sizeof(void*)*4, v___x_451_);
v___x_461_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_462_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__3, &l_Lake_leanSharedDynlibs___closed__3_once, _init_l_Lake_leanSharedDynlibs___closed__3);
v___x_463_ = l_System_FilePath_join(v___x_456_, v___x_462_);
v_lean1_464_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_464_, 0, v___x_463_);
lean_ctor_set(v_lean1_464_, 1, v___x_461_);
lean_ctor_set(v_lean1_464_, 2, v___x_459_);
lean_ctor_set(v_lean1_464_, 3, v___x_459_);
lean_ctor_set_uint8(v_lean1_464_, sizeof(void*)*4, v___x_451_);
v___x_465_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_466_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__5, &l_Lake_leanSharedDynlibs___closed__5_once, _init_l_Lake_leanSharedDynlibs___closed__5);
v___x_467_ = l_System_FilePath_join(v___x_456_, v___x_466_);
v_lean2_468_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_468_, 0, v___x_467_);
lean_ctor_set(v_lean2_468_, 1, v___x_465_);
lean_ctor_set(v_lean2_468_, 2, v___x_459_);
lean_ctor_set(v_lean2_468_, 3, v___x_459_);
lean_ctor_set_uint8(v_lean2_468_, sizeof(void*)*4, v___x_451_);
v___x_469_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_470_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__7, &l_Lake_leanSharedDynlibs___closed__7_once, _init_l_Lake_leanSharedDynlibs___closed__7);
v___x_471_ = l_System_FilePath_join(v___x_456_, v___x_470_);
v_lean3_472_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean3_472_, 0, v___x_471_);
lean_ctor_set(v_lean3_472_, 1, v___x_469_);
lean_ctor_set(v_lean3_472_, 2, v___x_459_);
lean_ctor_set(v_lean3_472_, 3, v___x_459_);
lean_ctor_set_uint8(v_lean3_472_, sizeof(void*)*4, v___x_451_);
v___x_473_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__4));
v___x_474_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__9, &l_Lake_leanSharedDynlibs___closed__9_once, _init_l_Lake_leanSharedDynlibs___closed__9);
v___x_475_ = l_System_FilePath_join(v___x_456_, v___x_474_);
v_lean_476_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_476_, 0, v___x_475_);
lean_ctor_set(v_lean_476_, 1, v___x_473_);
lean_ctor_set(v_lean_476_, 2, v___x_459_);
lean_ctor_set(v_lean_476_, 3, v___x_459_);
lean_ctor_set_uint8(v_lean_476_, sizeof(void*)*4, v___x_451_);
v___x_477_ = lean_unsigned_to_nat(5u);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_477_);
v___x_479_ = lean_array_push(v___x_478_, v_lean_476_);
v___x_480_ = lean_array_push(v___x_479_, v_lean3_472_);
v___x_481_ = lean_array_push(v___x_480_, v_lean2_468_);
v___x_482_ = lean_array_push(v___x_481_, v_lean1_464_);
v___x_483_ = lean_array_push(v___x_482_, v_init_460_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v_init_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_lean1_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_lean2_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_lean3_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_lean_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_484_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_485_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_486_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_487_ = l_System_FilePath_join(v_sysroot_450_, v___x_486_);
v___x_488_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__10));
lean_inc_ref_n(v___x_487_, 4);
v___x_489_ = l_System_FilePath_join(v___x_487_, v___x_488_);
v___x_490_ = 0;
v_init_491_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_491_, 0, v___x_489_);
lean_ctor_set(v_init_491_, 1, v___x_484_);
lean_ctor_set(v_init_491_, 2, v___x_485_);
lean_ctor_set(v_init_491_, 3, v___x_485_);
lean_ctor_set_uint8(v_init_491_, sizeof(void*)*4, v___x_490_);
v___x_492_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_mk_empty_array_with_capacity(v___x_493_);
lean_inc_ref_n(v_init_491_, 4);
v___x_495_ = lean_array_push(v___x_494_, v_init_491_);
v___x_496_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__11));
v___x_497_ = l_System_FilePath_join(v___x_487_, v___x_496_);
v_lean1_498_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_498_, 0, v___x_497_);
lean_ctor_set(v_lean1_498_, 1, v___x_492_);
lean_ctor_set(v_lean1_498_, 2, v___x_495_);
lean_ctor_set(v_lean1_498_, 3, v___x_485_);
lean_ctor_set_uint8(v_lean1_498_, sizeof(void*)*4, v___x_490_);
v___x_499_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_500_ = lean_unsigned_to_nat(2u);
v___x_501_ = lean_mk_empty_array_with_capacity(v___x_500_);
lean_inc_ref_n(v_lean1_498_, 3);
v___x_502_ = lean_array_push(v___x_501_, v_lean1_498_);
v___x_503_ = lean_array_push(v___x_502_, v_init_491_);
v___x_504_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__12));
v___x_505_ = l_System_FilePath_join(v___x_487_, v___x_504_);
v_lean2_506_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_506_, 0, v___x_505_);
lean_ctor_set(v_lean2_506_, 1, v___x_499_);
lean_ctor_set(v_lean2_506_, 2, v___x_503_);
lean_ctor_set(v_lean2_506_, 3, v___x_485_);
lean_ctor_set_uint8(v_lean2_506_, sizeof(void*)*4, v___x_490_);
v___x_507_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_508_ = lean_unsigned_to_nat(3u);
v___x_509_ = lean_mk_empty_array_with_capacity(v___x_508_);
lean_inc_ref_n(v_lean2_506_, 2);
v___x_510_ = lean_array_push(v___x_509_, v_lean2_506_);
v___x_511_ = lean_array_push(v___x_510_, v_lean1_498_);
v___x_512_ = lean_array_push(v___x_511_, v_init_491_);
v___x_513_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__13));
v___x_514_ = l_System_FilePath_join(v___x_487_, v___x_513_);
v_lean3_515_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean3_515_, 0, v___x_514_);
lean_ctor_set(v_lean3_515_, 1, v___x_507_);
lean_ctor_set(v_lean3_515_, 2, v___x_512_);
lean_ctor_set(v_lean3_515_, 3, v___x_485_);
lean_ctor_set_uint8(v_lean3_515_, sizeof(void*)*4, v___x_490_);
v___x_516_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__4));
v___x_517_ = lean_unsigned_to_nat(4u);
v___x_518_ = lean_mk_empty_array_with_capacity(v___x_517_);
lean_inc_ref(v_lean3_515_);
v___x_519_ = lean_array_push(v___x_518_, v_lean3_515_);
v___x_520_ = lean_array_push(v___x_519_, v_lean2_506_);
v___x_521_ = lean_array_push(v___x_520_, v_lean1_498_);
v___x_522_ = lean_array_push(v___x_521_, v_init_491_);
v___x_523_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__14));
v___x_524_ = l_System_FilePath_join(v___x_487_, v___x_523_);
v_lean_525_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_525_, 0, v___x_524_);
lean_ctor_set(v_lean_525_, 1, v___x_516_);
lean_ctor_set(v_lean_525_, 2, v___x_522_);
lean_ctor_set(v_lean_525_, 3, v___x_485_);
lean_ctor_set_uint8(v_lean_525_, sizeof(void*)*4, v___x_490_);
v___x_526_ = lean_unsigned_to_nat(5u);
v___x_527_ = lean_mk_empty_array_with_capacity(v___x_526_);
v___x_528_ = lean_array_push(v___x_527_, v_lean_525_);
v___x_529_ = lean_array_push(v___x_528_, v_lean3_515_);
v___x_530_ = lean_array_push(v___x_529_, v_lean2_506_);
v___x_531_ = lean_array_push(v___x_530_, v_lean1_498_);
v___x_532_ = lean_array_push(v___x_531_, v_init_491_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlib(lean_object* v_sysroot_533_){
_start:
{
lean_object* v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_534_ = l_Lake_leanSharedDynlibs(v_sysroot_533_);
v___x_535_ = ((size_t)0ULL);
v___x_536_ = lean_array_uget(v___x_534_, v___x_535_);
lean_dec_ref(v___x_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = l_Lake_sharedLibExt;
v___x_539_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_540_ = l_System_FilePath_addExtension(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_541_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = l_Lake_sharedLibExt;
v___x_544_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_545_ = l_System_FilePath_addExtension(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_546_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_549_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_550_ = l_System_FilePath_join(v___x_549_, v___x_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_552_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
v___x_553_ = l_System_FilePath_join(v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_555_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_556_ = l_System_FilePath_join(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_558_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_559_ = l_System_FilePath_join(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_562_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_563_ = l_System_FilePath_join(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__7(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_565_ = l_Lake_leanExe(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__8(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_567_ = l_Lake_leanirExe(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__9(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_569_ = l_Lake_leancExe(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__10(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_571_ = l_Lake_leantarExe(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__11(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_573_ = l_Lake_leanSharedDynlibs(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__12(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_575_ = l_Lake_leanSharedDynlib(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__16(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_580_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_581_ = lean_array_push(v___x_580_, v___x_579_);
return v___x_581_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__17(void){
_start:
{
uint8_t v___x_582_; lean_object* v___x_583_; 
v___x_582_ = 1;
v___x_583_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__18(void){
_start:
{
uint8_t v___x_584_; lean_object* v___x_585_; 
v___x_584_ = 0;
v___x_585_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__19(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_586_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_587_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_588_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_589_ = 1;
v___x_590_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_591_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_592_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__12, &l_Lake_instInhabitedLeanInstall_default___closed__12_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__12);
v___x_593_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_594_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__10, &l_Lake_instInhabitedLeanInstall_default___closed__10_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__10);
v___x_595_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__9, &l_Lake_instInhabitedLeanInstall_default___closed__9_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__9);
v___x_596_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__8, &l_Lake_instInhabitedLeanInstall_default___closed__8_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__8);
v___x_597_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__7, &l_Lake_instInhabitedLeanInstall_default___closed__7_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__7);
v___x_598_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_599_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_600_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
v___x_601_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_602_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__2, &l_Lake_instInhabitedLeanInstall_default___closed__2_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__2);
v___x_603_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_604_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
lean_ctor_set(v___x_604_, 2, v___x_602_);
lean_ctor_set(v___x_604_, 3, v___x_601_);
lean_ctor_set(v___x_604_, 4, v___x_600_);
lean_ctor_set(v___x_604_, 5, v___x_599_);
lean_ctor_set(v___x_604_, 6, v___x_598_);
lean_ctor_set(v___x_604_, 7, v___x_597_);
lean_ctor_set(v___x_604_, 8, v___x_596_);
lean_ctor_set(v___x_604_, 9, v___x_595_);
lean_ctor_set(v___x_604_, 10, v___x_594_);
lean_ctor_set(v___x_604_, 11, v___x_593_);
lean_ctor_set(v___x_604_, 12, v___x_592_);
lean_ctor_set(v___x_604_, 13, v___x_591_);
lean_ctor_set(v___x_604_, 14, v___x_590_);
lean_ctor_set(v___x_604_, 15, v___x_588_);
lean_ctor_set(v___x_604_, 16, v___x_587_);
lean_ctor_set(v___x_604_, 17, v___x_586_);
lean_ctor_set(v___x_604_, 18, v___x_588_);
lean_ctor_set(v___x_604_, 19, v___x_587_);
lean_ctor_set(v___x_604_, 20, v___x_586_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*21, v___x_589_);
return v___x_604_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
return v___x_605_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_dec(v_x_607_);
return v_x_608_;
}
else
{
lean_object* v_head_610_; lean_object* v_tail_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_622_; 
v_head_610_ = lean_ctor_get(v_x_609_, 0);
v_tail_611_ = lean_ctor_get(v_x_609_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_609_);
if (v_isSharedCheck_622_ == 0)
{
v___x_613_ = v_x_609_;
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_tail_611_);
lean_inc(v_head_610_);
lean_dec(v_x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
lean_inc(v_x_607_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 5);
lean_ctor_set(v___x_613_, 1, v_x_607_);
lean_ctor_set(v___x_613_, 0, v_x_608_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_x_608_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_x_607_);
v___x_616_ = v_reuseFailAlloc_621_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = l_String_quote(v_head_610_);
v___x_618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_616_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v_x_608_ = v___x_619_;
v_x_609_ = v_tail_611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
lean_dec(v_x_623_);
return v_x_624_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_638_; 
v_head_626_ = lean_ctor_get(v_x_625_, 0);
v_tail_627_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_638_ == 0)
{
v___x_629_ = v_x_625_;
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_tail_627_);
lean_inc(v_head_626_);
lean_dec(v_x_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
lean_inc(v_x_623_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 5);
lean_ctor_set(v___x_629_, 1, v_x_623_);
lean_ctor_set(v___x_629_, 0, v_x_624_);
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_x_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_x_623_);
v___x_632_ = v_reuseFailAlloc_637_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_633_ = l_String_quote(v_head_626_);
v___x_634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_632_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(v_x_623_, v___x_635_, v_tail_627_);
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(lean_object* v___y_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = l_String_quote(v___y_639_);
v___x_641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v___x_644_; 
lean_dec(v_x_643_);
v___x_644_ = lean_box(0);
return v___x_644_;
}
else
{
lean_object* v_tail_645_; 
v_tail_645_ = lean_ctor_get(v_x_642_, 1);
if (lean_obj_tag(v_tail_645_) == 0)
{
lean_object* v_head_646_; lean_object* v___x_647_; 
lean_dec(v_x_643_);
v_head_646_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_head_646_);
lean_dec_ref_known(v_x_642_, 2);
v___x_647_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_646_);
return v___x_647_;
}
else
{
lean_object* v_head_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_inc(v_tail_645_);
v_head_648_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_head_648_);
lean_dec_ref_known(v_x_642_, 2);
v___x_649_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_648_);
v___x_650_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(v_x_643_, v___x_649_, v_tail_645_);
return v___x_650_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0));
v___x_657_ = lean_string_length(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3);
v___x_659_ = lean_nat_to_int(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(lean_object* v_xs_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_668_ = lean_array_get_size(v_xs_667_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_nat_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_671_ = lean_array_to_list(v_xs_667_);
v___x_672_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_673_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(v___x_671_, v___x_672_);
v___x_674_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_675_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_673_);
v___x_677_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_674_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Std_Format_fill(v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; 
lean_dec_ref(v_xs_667_);
v___x_681_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_dec(v_x_682_);
return v_x_683_;
}
else
{
lean_object* v_head_685_; lean_object* v_tail_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_696_; 
v_head_685_ = lean_ctor_get(v_x_684_, 0);
v_tail_686_ = lean_ctor_get(v_x_684_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_696_ == 0)
{
v___x_688_ = v_x_684_;
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_tail_686_);
lean_inc(v_head_685_);
lean_dec(v_x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
lean_inc(v_x_682_);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 5);
lean_ctor_set(v___x_688_, 1, v_x_682_);
lean_ctor_set(v___x_688_, 0, v_x_683_);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_x_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_x_682_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = l_Lake_instReprDynlib_repr___redArg(v_head_685_);
v___x_693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v_x_683_ = v___x_693_;
v_x_684_ = v_tail_686_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_dec(v_x_697_);
return v_x_698_;
}
else
{
lean_object* v_head_700_; lean_object* v_tail_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_head_700_ = lean_ctor_get(v_x_699_, 0);
v_tail_701_ = lean_ctor_get(v_x_699_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_711_ == 0)
{
v___x_703_ = v_x_699_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_tail_701_);
lean_inc(v_head_700_);
lean_dec(v_x_699_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
lean_inc(v_x_697_);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 5);
lean_ctor_set(v___x_703_, 1, v_x_697_);
lean_ctor_set(v___x_703_, 0, v_x_698_);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_x_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_x_697_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = l_Lake_instReprDynlib_repr___redArg(v_head_700_);
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(v_x_697_, v___x_708_, v_tail_701_);
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v___x_714_; 
lean_dec(v_x_713_);
v___x_714_ = lean_box(0);
return v___x_714_;
}
else
{
lean_object* v_tail_715_; 
v_tail_715_ = lean_ctor_get(v_x_712_, 1);
if (lean_obj_tag(v_tail_715_) == 0)
{
lean_object* v_head_716_; lean_object* v___x_717_; 
lean_dec(v_x_713_);
v_head_716_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_head_716_);
lean_dec_ref_known(v_x_712_, 2);
v___x_717_ = l_Lake_instReprDynlib_repr___redArg(v_head_716_);
return v___x_717_;
}
else
{
lean_object* v_head_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_inc(v_tail_715_);
v_head_718_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_head_718_);
lean_dec_ref_known(v_x_712_, 2);
v___x_719_ = l_Lake_instReprDynlib_repr___redArg(v_head_718_);
v___x_720_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_713_, v___x_719_, v_tail_715_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_array_get_size(v_xs_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_725_ = lean_array_to_list(v_xs_721_);
v___x_726_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_727_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_725_, v___x_726_);
v___x_728_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_729_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_727_);
v___x_731_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_728_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Std_Format_fill(v___x_733_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; 
lean_dec_ref(v_xs_721_);
v___x_735_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_735_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(11u);
v___x_746_ = lean_nat_to_int(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(14u);
v___x_757_ = lean_nat_to_int(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(16u);
v___x_765_ = lean_nat_to_int(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(9u);
v___x_773_ = lean_nat_to_int(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(6u);
v___x_785_ = lean_nat_to_int(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_unsigned_to_nat(12u);
v___x_792_ = lean_nat_to_int(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(19u);
v___x_800_ = lean_nat_to_int(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(21u);
v___x_811_ = lean_nat_to_int(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_815_){
_start:
{
lean_object* v_sysroot_816_; lean_object* v_githash_817_; lean_object* v_srcDir_818_; lean_object* v_leanLibDir_819_; lean_object* v_includeDir_820_; lean_object* v_systemLibDir_821_; lean_object* v_binDir_822_; lean_object* v_lean_823_; lean_object* v_leanir_824_; lean_object* v_leanc_825_; lean_object* v_leantar_826_; lean_object* v_sharedDynlibs_827_; lean_object* v_sharedDynlib_828_; lean_object* v_ar_829_; lean_object* v_cc_830_; uint8_t v_customCc_831_; lean_object* v_cFlags_832_; lean_object* v_linkStaticFlags_833_; lean_object* v_linkSharedFlags_834_; lean_object* v_ccFlags_835_; lean_object* v_ccLinkStaticFlags_836_; lean_object* v_ccLinkSharedFlags_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_sysroot_816_ = lean_ctor_get(v_x_815_, 0);
lean_inc_ref(v_sysroot_816_);
v_githash_817_ = lean_ctor_get(v_x_815_, 1);
lean_inc_ref(v_githash_817_);
v_srcDir_818_ = lean_ctor_get(v_x_815_, 2);
lean_inc_ref(v_srcDir_818_);
v_leanLibDir_819_ = lean_ctor_get(v_x_815_, 3);
lean_inc_ref(v_leanLibDir_819_);
v_includeDir_820_ = lean_ctor_get(v_x_815_, 4);
lean_inc_ref(v_includeDir_820_);
v_systemLibDir_821_ = lean_ctor_get(v_x_815_, 5);
lean_inc_ref(v_systemLibDir_821_);
v_binDir_822_ = lean_ctor_get(v_x_815_, 6);
lean_inc_ref(v_binDir_822_);
v_lean_823_ = lean_ctor_get(v_x_815_, 7);
lean_inc_ref(v_lean_823_);
v_leanir_824_ = lean_ctor_get(v_x_815_, 8);
lean_inc_ref(v_leanir_824_);
v_leanc_825_ = lean_ctor_get(v_x_815_, 9);
lean_inc_ref(v_leanc_825_);
v_leantar_826_ = lean_ctor_get(v_x_815_, 10);
lean_inc_ref(v_leantar_826_);
v_sharedDynlibs_827_ = lean_ctor_get(v_x_815_, 11);
lean_inc_ref(v_sharedDynlibs_827_);
v_sharedDynlib_828_ = lean_ctor_get(v_x_815_, 12);
lean_inc_ref(v_sharedDynlib_828_);
v_ar_829_ = lean_ctor_get(v_x_815_, 13);
lean_inc_ref(v_ar_829_);
v_cc_830_ = lean_ctor_get(v_x_815_, 14);
lean_inc_ref(v_cc_830_);
v_customCc_831_ = lean_ctor_get_uint8(v_x_815_, sizeof(void*)*21);
v_cFlags_832_ = lean_ctor_get(v_x_815_, 15);
lean_inc_ref(v_cFlags_832_);
v_linkStaticFlags_833_ = lean_ctor_get(v_x_815_, 16);
lean_inc_ref(v_linkStaticFlags_833_);
v_linkSharedFlags_834_ = lean_ctor_get(v_x_815_, 17);
lean_inc_ref(v_linkSharedFlags_834_);
v_ccFlags_835_ = lean_ctor_get(v_x_815_, 18);
lean_inc_ref(v_ccFlags_835_);
v_ccLinkStaticFlags_836_ = lean_ctor_get(v_x_815_, 19);
lean_inc_ref(v_ccLinkStaticFlags_836_);
v_ccLinkSharedFlags_837_ = lean_ctor_get(v_x_815_, 20);
lean_inc_ref(v_ccLinkSharedFlags_837_);
lean_dec_ref(v_x_815_);
v___x_838_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_839_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_840_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_843_ = l_String_quote(v_sysroot_816_);
v___x_844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
v___x_845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_842_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Repr_addAppParen(v___x_845_, v___x_841_);
v___x_847_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_840_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = 0;
v___x_849_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___x_848_);
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_839_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_box(1);
v___x_854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_838_);
v___x_858_ = l_String_quote(v_githash_817_);
v___x_859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___x_860_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_840_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*1, v___x_848_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_857_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_851_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_853_);
v___x_865_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_838_);
v___x_868_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_869_ = l_String_quote(v_srcDir_818_);
v___x_870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_842_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Repr_addAppParen(v___x_871_, v___x_841_);
v___x_873_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_868_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*1, v___x_848_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_867_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_851_);
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_853_);
v___x_878_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_838_);
v___x_881_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_882_ = l_String_quote(v_leanLibDir_819_);
v___x_883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_842_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Repr_addAppParen(v___x_884_, v___x_841_);
v___x_886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_881_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_848_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_880_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_851_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_853_);
v___x_891_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_838_);
v___x_894_ = l_String_quote(v_includeDir_820_);
v___x_895_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_842_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Repr_addAppParen(v___x_896_, v___x_841_);
v___x_898_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_881_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*1, v___x_848_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_893_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_851_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_853_);
v___x_903_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_838_);
v___x_906_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_907_ = l_String_quote(v_systemLibDir_821_);
v___x_908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_842_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Repr_addAppParen(v___x_909_, v___x_841_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_848_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_905_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_851_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_853_);
v___x_916_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_838_);
v___x_919_ = l_String_quote(v_binDir_822_);
v___x_920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_842_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Repr_addAppParen(v___x_921_, v___x_841_);
v___x_923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_868_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*1, v___x_848_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_918_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_851_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_853_);
v___x_928_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_838_);
v___x_931_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_932_ = l_String_quote(v_lean_823_);
v___x_933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_842_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Repr_addAppParen(v___x_934_, v___x_841_);
v___x_936_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_931_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*1, v___x_848_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_930_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_851_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_853_);
v___x_941_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_838_);
v___x_944_ = l_String_quote(v_leanir_824_);
v___x_945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_842_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Repr_addAppParen(v___x_946_, v___x_841_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_868_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_848_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_943_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_851_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_853_);
v___x_953_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_838_);
v___x_956_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_957_ = l_String_quote(v_leanc_825_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_842_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Repr_addAppParen(v___x_959_, v___x_841_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_848_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_955_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_851_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_853_);
v___x_966_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_838_);
v___x_969_ = l_String_quote(v_leantar_826_);
v___x_970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_842_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Repr_addAppParen(v___x_971_, v___x_841_);
v___x_973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_840_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*1, v___x_848_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_968_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_851_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_853_);
v___x_978_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_838_);
v___x_981_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_982_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_sharedDynlibs_827_);
v___x_983_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*1, v___x_848_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_980_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_851_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_853_);
v___x_988_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_838_);
v___x_991_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_828_);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_906_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_848_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_990_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_851_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_853_);
v___x_997_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_838_);
v___x_1000_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__27, &l_Lake_instReprLeanInstall_repr___redArg___closed__27_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27);
v___x_1001_ = l_String_quote(v_ar_829_);
v___x_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_842_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Repr_addAppParen(v___x_1003_, v___x_841_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1000_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_848_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_999_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_851_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_853_);
v___x_1010_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__28));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_838_);
v___x_1013_ = l_String_quote(v_cc_830_);
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_842_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Repr_addAppParen(v___x_1015_, v___x_841_);
v___x_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1000_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_848_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1012_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_851_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_853_);
v___x_1022_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_838_);
v___x_1025_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__31, &l_Lake_instReprLeanInstall_repr___redArg___closed__31_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31);
v___x_1026_ = l_Bool_repr___redArg(v_customCc_831_);
v___x_1027_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*1, v___x_848_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1024_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_851_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_853_);
v___x_1032_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__33));
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_838_);
v___x_1035_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_cFlags_832_);
v___x_1036_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_868_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*1, v___x_848_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1034_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_851_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_853_);
v___x_1041_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__35));
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_838_);
v___x_1044_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__36, &l_Lake_instReprLeanInstall_repr___redArg___closed__36_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36);
v___x_1045_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkStaticFlags_833_);
v___x_1046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*1, v___x_848_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1043_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_851_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_853_);
v___x_1051_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__38));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_838_);
v___x_1054_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkSharedFlags_834_);
v___x_1055_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1044_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*1, v___x_848_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1053_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_851_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_853_);
v___x_1060_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__40));
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_838_);
v___x_1063_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccFlags_835_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_840_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v___x_848_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1062_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_851_);
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_853_);
v___x_1069_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__42));
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_838_);
v___x_1072_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__43, &l_Lake_instReprLeanInstall_repr___redArg___closed__43_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43);
v___x_1073_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkStaticFlags_836_);
v___x_1074_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*1, v___x_848_);
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1071_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_851_);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_853_);
v___x_1079_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__45));
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_838_);
v___x_1082_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkSharedFlags_837_);
v___x_1083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1072_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v___x_848_);
v___x_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1081_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1087_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1085_);
v___x_1089_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1086_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_848_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_1093_, lean_object* v_prec_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_1096_, lean_object* v_prec_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lake_instReprLeanInstall_repr(v_x_1096_, v_prec_1097_);
lean_dec(v_prec_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib(lean_object* v_self_1101_){
_start:
{
lean_object* v_sharedDynlib_1102_; lean_object* v_path_1103_; 
v_sharedDynlib_1102_ = lean_ctor_get(v_self_1101_, 12);
v_path_1103_ = lean_ctor_get(v_sharedDynlib_1102_, 0);
lean_inc_ref(v_path_1103_);
return v_path_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib___boxed(lean_object* v_self_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_LeanInstall_sharedLib(v_self_1104_);
lean_dec_ref(v_self_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_initSharedLib(lean_object* v_self_1106_){
_start:
{
lean_object* v_sysroot_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_sysroot_1107_ = lean_ctor_get(v_self_1106_, 0);
lean_inc_ref(v_sysroot_1107_);
lean_dec_ref(v_self_1106_);
v___x_1108_ = l_Lake_leanSharedLibDir(v_sysroot_1107_);
v___x_1109_ = l_Lake_initSharedLib;
v___x_1110_ = l_System_FilePath_join(v___x_1108_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_System_Platform_isWindows;
if (v___x_1112_ == 0)
{
lean_object* v_leanLibDir_1113_; lean_object* v_systemLibDir_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_leanLibDir_1113_ = lean_ctor_get(v_self_1111_, 3);
v_systemLibDir_1114_ = lean_ctor_get(v_self_1111_, 5);
v___x_1115_ = lean_box(0);
lean_inc_ref(v_systemLibDir_1114_);
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_systemLibDir_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_inc_ref(v_leanLibDir_1113_);
v___x_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_leanLibDir_1113_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
return v___x_1117_;
}
else
{
lean_object* v_binDir_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_binDir_1118_ = lean_ctor_get(v_self_1111_, 6);
v___x_1119_ = lean_box(0);
lean_inc_ref(v_binDir_1118_);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_binDir_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lake_LeanInstall_sharedLibPath(v_self_1121_);
lean_dec_ref(v_self_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_1123_){
_start:
{
uint8_t v_customCc_1124_; 
v_customCc_1124_ = lean_ctor_get_uint8(v_self_1123_, sizeof(void*)*21);
if (v_customCc_1124_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
else
{
lean_object* v_cc_1126_; lean_object* v___x_1127_; 
v_cc_1126_ = lean_ctor_get(v_self_1123_, 14);
lean_inc_ref(v_cc_1126_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_cc_1126_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lake_LeanInstall_leanCc_x3f(v_self_1128_);
lean_dec_ref(v_self_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_1130_, lean_object* v_self_1131_){
_start:
{
if (v_shared_1130_ == 0)
{
lean_object* v_ccLinkStaticFlags_1132_; 
v_ccLinkStaticFlags_1132_ = lean_ctor_get(v_self_1131_, 19);
lean_inc_ref(v_ccLinkStaticFlags_1132_);
return v_ccLinkStaticFlags_1132_;
}
else
{
lean_object* v_ccLinkSharedFlags_1133_; 
v_ccLinkSharedFlags_1133_ = lean_ctor_get(v_self_1131_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1133_);
return v_ccLinkSharedFlags_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_1134_, lean_object* v_self_1135_){
_start:
{
uint8_t v_shared_boxed_1136_; lean_object* v_res_1137_; 
v_shared_boxed_1136_ = lean_unbox(v_shared_1134_);
v_res_1137_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_1136_, v_self_1135_);
lean_dec_ref(v_self_1135_);
return v_res_1137_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = l_System_FilePath_exeExtension;
v___x_1140_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1141_ = l_System_FilePath_addExtension(v___x_1140_, v___x_1139_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_1142_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = l_Lake_defaultBuildDir;
v___x_1144_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1145_ = l_System_FilePath_join(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__1(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = l_Lake_defaultBinDir;
v___x_1147_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1148_ = l_System_FilePath_join(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__2(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = l_Lake_defaultLeanLibDir;
v___x_1150_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1151_ = l_System_FilePath_join(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__4(void){
_start:
{
uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = 0;
v___x_1154_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1155_ = l_Lake_nameToSharedLib(v___x_1154_, v___x_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__5(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
v___x_1157_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1158_ = l_System_FilePath_join(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__6(void){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1160_ = 0;
v___x_1161_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1162_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__5, &l_Lake_instInhabitedLakeInstall_default___closed__5_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__5);
v___x_1163_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1161_);
lean_ctor_set(v___x_1163_, 2, v___x_1159_);
lean_ctor_set(v___x_1163_, 3, v___x_1159_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*4, v___x_1160_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__7(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = l_Lake_lakeExe;
v___x_1165_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1166_ = l_System_FilePath_join(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__8(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1167_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__7, &l_Lake_instInhabitedLakeInstall_default___closed__7_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__7);
v___x_1168_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__6, &l_Lake_instInhabitedLakeInstall_default___closed__6_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__6);
v___x_1169_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1170_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1171_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1172_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
lean_ctor_set(v___x_1172_, 2, v___x_1170_);
lean_ctor_set(v___x_1172_, 3, v___x_1169_);
lean_ctor_set(v___x_1172_, 4, v___x_1168_);
lean_ctor_set(v___x_1172_, 5, v___x_1167_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__8, &l_Lake_instInhabitedLakeInstall_default___closed__8_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__8);
return v___x_1173_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_1180_){
_start:
{
lean_object* v_home_1181_; lean_object* v_srcDir_1182_; lean_object* v_binDir_1183_; lean_object* v_libDir_1184_; lean_object* v_sharedDynlib_1185_; lean_object* v_lake_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_home_1181_ = lean_ctor_get(v_x_1180_, 0);
lean_inc_ref(v_home_1181_);
v_srcDir_1182_ = lean_ctor_get(v_x_1180_, 1);
lean_inc_ref(v_srcDir_1182_);
v_binDir_1183_ = lean_ctor_get(v_x_1180_, 2);
lean_inc_ref(v_binDir_1183_);
v_libDir_1184_ = lean_ctor_get(v_x_1180_, 3);
lean_inc_ref(v_libDir_1184_);
v_sharedDynlib_1185_ = lean_ctor_get(v_x_1180_, 4);
lean_inc_ref(v_sharedDynlib_1185_);
v_lake_1186_ = lean_ctor_get(v_x_1180_, 5);
lean_inc_ref(v_lake_1186_);
lean_dec_ref(v_x_1180_);
v___x_1187_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_1188_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_1189_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_1192_ = l_String_quote(v_home_1181_);
v___x_1193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1191_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = l_Repr_addAppParen(v___x_1194_, v___x_1190_);
v___x_1196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1189_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = 0;
v___x_1198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*1, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1188_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_box(1);
v___x_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1187_);
v___x_1207_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_1208_ = l_String_quote(v_srcDir_1182_);
v___x_1209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1191_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = l_Repr_addAppParen(v___x_1210_, v___x_1190_);
v___x_1212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1207_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*1, v___x_1197_);
v___x_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1206_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1200_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1202_);
v___x_1217_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1187_);
v___x_1220_ = l_String_quote(v_binDir_1183_);
v___x_1221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1191_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = l_Repr_addAppParen(v___x_1222_, v___x_1190_);
v___x_1224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1207_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*1, v___x_1197_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1219_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1200_);
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v___x_1202_);
v___x_1229_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___x_1187_);
v___x_1232_ = l_String_quote(v_libDir_1184_);
v___x_1233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1191_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Repr_addAppParen(v___x_1234_, v___x_1190_);
v___x_1236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1207_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*1, v___x_1197_);
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1231_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___x_1200_);
v___x_1240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1202_);
v___x_1241_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___x_1187_);
v___x_1244_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_1245_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_1185_);
v___x_1246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*1, v___x_1197_);
v___x_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1243_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1200_);
v___x_1250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1202_);
v___x_1251_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__2));
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1187_);
v___x_1254_ = l_String_quote(v_lake_1186_);
v___x_1255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1191_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Repr_addAppParen(v___x_1256_, v___x_1190_);
v___x_1258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1189_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*1, v___x_1197_);
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1253_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1262_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1260_);
v___x_1264_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1261_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*1, v___x_1197_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_1268_, lean_object* v_prec_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_1271_, lean_object* v_prec_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lake_instReprLakeInstall_repr(v_x_1271_, v_prec_1272_);
lean_dec(v_prec_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_1276_){
_start:
{
lean_object* v_sharedDynlib_1277_; lean_object* v_path_1278_; 
v_sharedDynlib_1277_ = lean_ctor_get(v_self_1276_, 4);
v_path_1278_ = lean_ctor_get(v_sharedDynlib_1277_, 0);
lean_inc_ref(v_path_1278_);
return v_path_1278_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lake_LakeInstall_sharedLib(v_self_1279_);
lean_dec_ref(v_self_1279_);
return v_res_1280_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__2(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = l_Lake_sharedLibExt;
v___x_1284_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1285_ = lean_string_append(v___x_1284_, v___x_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_1287_){
_start:
{
lean_object* v_sysroot_1288_; lean_object* v_srcDir_1289_; lean_object* v_leanLibDir_1290_; lean_object* v_binDir_1291_; lean_object* v_sharedDynlibs_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___y_1296_; uint8_t v___x_1304_; 
v_sysroot_1288_ = lean_ctor_get(v_lean_1287_, 0);
lean_inc_ref(v_sysroot_1288_);
v_srcDir_1289_ = lean_ctor_get(v_lean_1287_, 2);
lean_inc_ref(v_srcDir_1289_);
v_leanLibDir_1290_ = lean_ctor_get(v_lean_1287_, 3);
lean_inc_ref(v_leanLibDir_1290_);
v_binDir_1291_ = lean_ctor_get(v_lean_1287_, 6);
lean_inc_ref(v_binDir_1291_);
v_sharedDynlibs_1292_ = lean_ctor_get(v_lean_1287_, 11);
lean_inc_ref(v_sharedDynlibs_1292_);
lean_dec_ref(v_lean_1287_);
v___x_1293_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1294_ = l_System_FilePath_join(v_srcDir_1289_, v___x_1293_);
v___x_1304_ = l_System_Platform_isWindows;
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__2, &l_Lake_LakeInstall_ofLean___closed__2_once, _init_l_Lake_LakeInstall_ofLean___closed__2);
lean_inc_ref(v_leanLibDir_1290_);
v___x_1306_ = l_System_FilePath_join(v_leanLibDir_1290_, v___x_1305_);
v___y_1296_ = v___x_1306_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__3));
lean_inc_ref(v_binDir_1291_);
v___x_1308_ = l_System_FilePath_join(v_binDir_1291_, v___x_1307_);
v___y_1296_ = v___x_1308_;
goto v___jp_1295_;
}
v___jp_1295_:
{
lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1297_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_1298_ = 0;
v___x_1299_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1300_, 0, v___y_1296_);
lean_ctor_set(v___x_1300_, 1, v___x_1297_);
lean_ctor_set(v___x_1300_, 2, v_sharedDynlibs_1292_);
lean_ctor_set(v___x_1300_, 3, v___x_1299_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*4, v___x_1298_);
v___x_1301_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_1291_);
v___x_1302_ = l_System_FilePath_join(v_binDir_1291_, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1303_, 0, v_sysroot_1288_);
lean_ctor_set(v___x_1303_, 1, v___x_1294_);
lean_ctor_set(v___x_1303_, 2, v_binDir_1291_);
lean_ctor_set(v___x_1303_, 3, v_leanLibDir_1290_);
lean_ctor_set(v___x_1303_, 4, v___x_1300_);
lean_ctor_set(v___x_1303_, 5, v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_1313_ = lean_io_getenv(v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 1)
{
lean_object* v_val_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1341_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1341_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_val_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1341_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___y_1321_; 
v___x_1318_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_1319_ = lean_io_getenv(v___x_1318_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_1321_ = v___x_1339_;
goto v___jp_1320_;
}
else
{
lean_object* v_val_1340_; 
v_val_1340_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v___x_1319_, 1);
v___y_1321_ = v_val_1340_;
goto v___jp_1320_;
}
v___jp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_startInclusive_1326_; lean_object* v_endExclusive_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_string_utf8_byte_size(v___y_1321_);
lean_inc_ref(v___y_1321_);
v___x_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1324_, 0, v___y_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
lean_ctor_set(v___x_1324_, 2, v___x_1323_);
v___x_1325_ = l_String_Slice_trimAscii(v___x_1324_);
v_startInclusive_1326_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_startInclusive_1326_);
v_endExclusive_1327_ = lean_ctor_get(v___x_1325_, 2);
lean_inc(v_endExclusive_1327_);
lean_dec_ref(v___x_1325_);
v___x_1328_ = lean_nat_sub(v_endExclusive_1327_, v_startInclusive_1326_);
lean_dec(v_startInclusive_1326_);
lean_dec(v_endExclusive_1327_);
v___x_1329_ = lean_nat_dec_eq(v___x_1328_, v___x_1322_);
lean_dec(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1330_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
lean_inc_n(v_val_1314_, 2);
v___x_1331_ = l_System_FilePath_join(v_val_1314_, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_1333_ = l_System_FilePath_join(v_val_1314_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1334_, 0, v_val_1314_);
lean_ctor_set(v___x_1334_, 1, v___y_1321_);
lean_ctor_set(v___x_1334_, 2, v___x_1331_);
lean_ctor_set(v___x_1334_, 3, v___x_1333_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1334_);
v___x_1336_ = v___x_1316_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v___x_1338_; 
lean_dec_ref(v___y_1321_);
lean_del_object(v___x_1316_);
lean_dec(v_val_1314_);
v___x_1338_ = lean_box(0);
return v___x_1338_;
}
}
}
}
else
{
lean_object* v___x_1342_; 
lean_dec(v___x_1313_);
v___x_1342_ = lean_box(0);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lake_findElanInstall_x3f();
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1356_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1357_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1361_ = 1;
v___x_1362_ = 0;
v___x_1363_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1363_, 0, v___x_1356_);
lean_ctor_set(v___x_1363_, 1, v_lean_1354_);
lean_ctor_set(v___x_1363_, 2, v___x_1357_);
lean_ctor_set(v___x_1363_, 3, v___x_1358_);
lean_ctor_set(v___x_1363_, 4, v___x_1360_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*5, v___x_1361_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*5 + 1, v___x_1362_);
v___x_1364_ = l_IO_Process_output(v___x_1363_, v___x_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1383_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1383_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1383_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
uint32_t v_exitCode_1369_; lean_object* v_stdout_1370_; uint32_t v___x_1371_; uint8_t v___x_1372_; 
v_exitCode_1369_ = lean_ctor_get_uint32(v_a_1365_, sizeof(void*)*2);
v_stdout_1370_ = lean_ctor_get(v_a_1365_, 0);
lean_inc_ref(v_stdout_1370_);
lean_dec(v_a_1365_);
v___x_1371_ = 0;
v___x_1372_ = lean_uint32_dec_eq(v_exitCode_1369_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v_stdout_1370_);
lean_del_object(v___x_1367_);
return v___x_1358_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_str_1376_; lean_object* v_startInclusive_1377_; lean_object* v_endExclusive_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1373_ = lean_string_utf8_byte_size(v_stdout_1370_);
v___x_1374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1374_, 0, v_stdout_1370_);
lean_ctor_set(v___x_1374_, 1, v___x_1359_);
lean_ctor_set(v___x_1374_, 2, v___x_1373_);
v___x_1375_ = l_String_Slice_trimAscii(v___x_1374_);
v_str_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_str_1376_);
v_startInclusive_1377_ = lean_ctor_get(v___x_1375_, 1);
lean_inc(v_startInclusive_1377_);
v_endExclusive_1378_ = lean_ctor_get(v___x_1375_, 2);
lean_inc(v_endExclusive_1378_);
lean_dec_ref(v___x_1375_);
v___x_1379_ = lean_string_utf8_extract_fast(v_str_1376_, v_startInclusive_1377_, v_endExclusive_1378_);
lean_dec(v_endExclusive_1378_);
lean_dec(v_startInclusive_1377_);
lean_dec_ref(v_str_1376_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 1);
lean_ctor_set(v___x_1367_, 0, v___x_1379_);
v___x_1381_ = v___x_1367_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1364_, 1);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lake_findLeanSysroot_x3f(v_lean_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1394_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1395_ = l_Lake_leanExe(v_sysroot_1392_);
v___x_1396_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1400_ = 1;
v___x_1401_ = 0;
v___x_1402_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1402_, 0, v___x_1394_);
lean_ctor_set(v___x_1402_, 1, v___x_1395_);
lean_ctor_set(v___x_1402_, 2, v___x_1396_);
lean_ctor_set(v___x_1402_, 3, v___x_1397_);
lean_ctor_set(v___x_1402_, 4, v___x_1399_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*5, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*5 + 1, v___x_1401_);
v___x_1403_ = l_IO_Process_output(v___x_1402_, v___x_1397_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v_stdout_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_str_1409_; lean_object* v_startInclusive_1410_; lean_object* v_endExclusive_1411_; lean_object* v___x_1412_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v_stdout_1405_ = lean_ctor_get(v_a_1404_, 0);
lean_inc_ref(v_stdout_1405_);
lean_dec(v_a_1404_);
v___x_1406_ = lean_string_utf8_byte_size(v_stdout_1405_);
v___x_1407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1407_, 0, v_stdout_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1398_);
lean_ctor_set(v___x_1407_, 2, v___x_1406_);
v___x_1408_ = l_String_Slice_trimAscii(v___x_1407_);
v_str_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_str_1409_);
v_startInclusive_1410_ = lean_ctor_get(v___x_1408_, 1);
lean_inc(v_startInclusive_1410_);
v_endExclusive_1411_ = lean_ctor_get(v___x_1408_, 2);
lean_inc(v_endExclusive_1411_);
lean_dec_ref(v___x_1408_);
v___x_1412_ = lean_string_utf8_extract_fast(v_str_1409_, v_startInclusive_1410_, v_endExclusive_1411_);
lean_dec(v_endExclusive_1411_);
lean_dec(v_startInclusive_1410_);
lean_dec_ref(v_str_1409_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
lean_dec_ref_known(v___x_1403_, 1);
v___x_1413_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1422_ = lean_io_getenv(v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 1)
{
lean_object* v_val_1423_; 
lean_dec_ref(v_sysroot_1419_);
v_val_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v___x_1422_, 1);
return v_val_1423_;
}
else
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
lean_dec(v___x_1422_);
v___x_1424_ = l_Lake_leanArExe(v_sysroot_1419_);
v___x_1425_ = l_System_FilePath_pathExists(v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v___x_1424_);
v___x_1426_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1427_ = lean_io_getenv(v___x_1426_);
if (lean_obj_tag(v___x_1427_) == 1)
{
lean_object* v_val_1428_; 
v_val_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_val_1428_);
lean_dec_ref_known(v___x_1427_, 1);
return v_val_1428_;
}
else
{
lean_object* v___x_1429_; 
lean_dec(v___x_1427_);
v___x_1429_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
return v___x_1429_;
}
}
else
{
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1433_, lean_object* v_i_1434_, lean_object* v_cc_1435_){
_start:
{
lean_object* v_sysroot_1436_; lean_object* v_githash_1437_; lean_object* v_srcDir_1438_; lean_object* v_leanLibDir_1439_; lean_object* v_includeDir_1440_; lean_object* v_systemLibDir_1441_; lean_object* v_binDir_1442_; lean_object* v_lean_1443_; lean_object* v_leanir_1444_; lean_object* v_leanc_1445_; lean_object* v_leantar_1446_; lean_object* v_sharedDynlibs_1447_; lean_object* v_sharedDynlib_1448_; lean_object* v_ar_1449_; lean_object* v_cFlags_1450_; lean_object* v_linkStaticFlags_1451_; lean_object* v_linkSharedFlags_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1465_; 
v_sysroot_1436_ = lean_ctor_get(v_i_1434_, 0);
v_githash_1437_ = lean_ctor_get(v_i_1434_, 1);
v_srcDir_1438_ = lean_ctor_get(v_i_1434_, 2);
v_leanLibDir_1439_ = lean_ctor_get(v_i_1434_, 3);
v_includeDir_1440_ = lean_ctor_get(v_i_1434_, 4);
v_systemLibDir_1441_ = lean_ctor_get(v_i_1434_, 5);
v_binDir_1442_ = lean_ctor_get(v_i_1434_, 6);
v_lean_1443_ = lean_ctor_get(v_i_1434_, 7);
v_leanir_1444_ = lean_ctor_get(v_i_1434_, 8);
v_leanc_1445_ = lean_ctor_get(v_i_1434_, 9);
v_leantar_1446_ = lean_ctor_get(v_i_1434_, 10);
v_sharedDynlibs_1447_ = lean_ctor_get(v_i_1434_, 11);
v_sharedDynlib_1448_ = lean_ctor_get(v_i_1434_, 12);
v_ar_1449_ = lean_ctor_get(v_i_1434_, 13);
v_cFlags_1450_ = lean_ctor_get(v_i_1434_, 15);
v_linkStaticFlags_1451_ = lean_ctor_get(v_i_1434_, 16);
v_linkSharedFlags_1452_ = lean_ctor_get(v_i_1434_, 17);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_i_1434_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1466_ = lean_ctor_get(v_i_1434_, 20);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_i_1434_, 19);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_i_1434_, 18);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_i_1434_, 14);
lean_dec(v_unused_1469_);
v___x_1454_ = v_i_1434_;
v_isShared_1455_ = v_isSharedCheck_1465_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_linkSharedFlags_1452_);
lean_inc(v_linkStaticFlags_1451_);
lean_inc(v_cFlags_1450_);
lean_inc(v_ar_1449_);
lean_inc(v_sharedDynlib_1448_);
lean_inc(v_sharedDynlibs_1447_);
lean_inc(v_leantar_1446_);
lean_inc(v_leanc_1445_);
lean_inc(v_leanir_1444_);
lean_inc(v_lean_1443_);
lean_inc(v_binDir_1442_);
lean_inc(v_systemLibDir_1441_);
lean_inc(v_includeDir_1440_);
lean_inc(v_leanLibDir_1439_);
lean_inc(v_srcDir_1438_);
lean_inc(v_githash_1437_);
lean_inc(v_sysroot_1436_);
lean_dec(v_i_1434_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1465_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_ccLinkFlags_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v_ccLinkFlags_1456_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1433_);
v___x_1457_ = 0;
v___x_1458_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1433_);
lean_inc_ref(v_cFlags_1450_);
v___x_1459_ = l_Array_append___redArg(v_cFlags_1450_, v___x_1458_);
lean_dec_ref(v___x_1458_);
lean_inc_ref(v_ccLinkFlags_1456_);
v___x_1460_ = l_Array_append___redArg(v_ccLinkFlags_1456_, v_linkStaticFlags_1451_);
v___x_1461_ = l_Array_append___redArg(v_ccLinkFlags_1456_, v_linkSharedFlags_1452_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 20, v___x_1461_);
lean_ctor_set(v___x_1454_, 19, v___x_1460_);
lean_ctor_set(v___x_1454_, 18, v___x_1459_);
lean_ctor_set(v___x_1454_, 14, v_cc_1435_);
v___x_1463_ = v___x_1454_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_sysroot_1436_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_githash_1437_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_srcDir_1438_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_leanLibDir_1439_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_includeDir_1440_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v_systemLibDir_1441_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_binDir_1442_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_lean_1443_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_leanir_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 9, v_leanc_1445_);
lean_ctor_set(v_reuseFailAlloc_1464_, 10, v_leantar_1446_);
lean_ctor_set(v_reuseFailAlloc_1464_, 11, v_sharedDynlibs_1447_);
lean_ctor_set(v_reuseFailAlloc_1464_, 12, v_sharedDynlib_1448_);
lean_ctor_set(v_reuseFailAlloc_1464_, 13, v_ar_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 14, v_cc_1435_);
lean_ctor_set(v_reuseFailAlloc_1464_, 15, v_cFlags_1450_);
lean_ctor_set(v_reuseFailAlloc_1464_, 16, v_linkStaticFlags_1451_);
lean_ctor_set(v_reuseFailAlloc_1464_, 17, v_linkSharedFlags_1452_);
lean_ctor_set(v_reuseFailAlloc_1464_, 18, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1464_, 19, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1464_, 20, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*21, v___x_1457_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1470_, lean_object* v_i_1471_, lean_object* v_cc_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1470_, v_i_1471_, v_cc_1472_);
lean_dec_ref(v_sysroot_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1474_, lean_object* v_cc_1475_){
_start:
{
lean_object* v_sysroot_1476_; lean_object* v_githash_1477_; lean_object* v_srcDir_1478_; lean_object* v_leanLibDir_1479_; lean_object* v_includeDir_1480_; lean_object* v_systemLibDir_1481_; lean_object* v_binDir_1482_; lean_object* v_lean_1483_; lean_object* v_leanir_1484_; lean_object* v_leanc_1485_; lean_object* v_leantar_1486_; lean_object* v_sharedDynlibs_1487_; lean_object* v_sharedDynlib_1488_; lean_object* v_ar_1489_; uint8_t v_customCc_1490_; lean_object* v_cFlags_1491_; lean_object* v_linkStaticFlags_1492_; lean_object* v_linkSharedFlags_1493_; lean_object* v_ccFlags_1494_; lean_object* v_ccLinkStaticFlags_1495_; lean_object* v_ccLinkSharedFlags_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_sysroot_1476_ = lean_ctor_get(v_i_1474_, 0);
v_githash_1477_ = lean_ctor_get(v_i_1474_, 1);
v_srcDir_1478_ = lean_ctor_get(v_i_1474_, 2);
v_leanLibDir_1479_ = lean_ctor_get(v_i_1474_, 3);
v_includeDir_1480_ = lean_ctor_get(v_i_1474_, 4);
v_systemLibDir_1481_ = lean_ctor_get(v_i_1474_, 5);
v_binDir_1482_ = lean_ctor_get(v_i_1474_, 6);
v_lean_1483_ = lean_ctor_get(v_i_1474_, 7);
v_leanir_1484_ = lean_ctor_get(v_i_1474_, 8);
v_leanc_1485_ = lean_ctor_get(v_i_1474_, 9);
v_leantar_1486_ = lean_ctor_get(v_i_1474_, 10);
v_sharedDynlibs_1487_ = lean_ctor_get(v_i_1474_, 11);
v_sharedDynlib_1488_ = lean_ctor_get(v_i_1474_, 12);
v_ar_1489_ = lean_ctor_get(v_i_1474_, 13);
v_customCc_1490_ = lean_ctor_get_uint8(v_i_1474_, sizeof(void*)*21);
v_cFlags_1491_ = lean_ctor_get(v_i_1474_, 15);
v_linkStaticFlags_1492_ = lean_ctor_get(v_i_1474_, 16);
v_linkSharedFlags_1493_ = lean_ctor_get(v_i_1474_, 17);
v_ccFlags_1494_ = lean_ctor_get(v_i_1474_, 18);
v_ccLinkStaticFlags_1495_ = lean_ctor_get(v_i_1474_, 19);
v_ccLinkSharedFlags_1496_ = lean_ctor_get(v_i_1474_, 20);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_i_1474_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_i_1474_, 14);
lean_dec(v_unused_1504_);
v___x_1498_ = v_i_1474_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1496_);
lean_inc(v_ccLinkStaticFlags_1495_);
lean_inc(v_ccFlags_1494_);
lean_inc(v_linkSharedFlags_1493_);
lean_inc(v_linkStaticFlags_1492_);
lean_inc(v_cFlags_1491_);
lean_inc(v_ar_1489_);
lean_inc(v_sharedDynlib_1488_);
lean_inc(v_sharedDynlibs_1487_);
lean_inc(v_leantar_1486_);
lean_inc(v_leanc_1485_);
lean_inc(v_leanir_1484_);
lean_inc(v_lean_1483_);
lean_inc(v_binDir_1482_);
lean_inc(v_systemLibDir_1481_);
lean_inc(v_includeDir_1480_);
lean_inc(v_leanLibDir_1479_);
lean_inc(v_srcDir_1478_);
lean_inc(v_githash_1477_);
lean_inc(v_sysroot_1476_);
lean_dec(v_i_1474_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 14, v_cc_1475_);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_sysroot_1476_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_githash_1477_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_srcDir_1478_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_leanLibDir_1479_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_includeDir_1480_);
lean_ctor_set(v_reuseFailAlloc_1502_, 5, v_systemLibDir_1481_);
lean_ctor_set(v_reuseFailAlloc_1502_, 6, v_binDir_1482_);
lean_ctor_set(v_reuseFailAlloc_1502_, 7, v_lean_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 8, v_leanir_1484_);
lean_ctor_set(v_reuseFailAlloc_1502_, 9, v_leanc_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 10, v_leantar_1486_);
lean_ctor_set(v_reuseFailAlloc_1502_, 11, v_sharedDynlibs_1487_);
lean_ctor_set(v_reuseFailAlloc_1502_, 12, v_sharedDynlib_1488_);
lean_ctor_set(v_reuseFailAlloc_1502_, 13, v_ar_1489_);
lean_ctor_set(v_reuseFailAlloc_1502_, 14, v_cc_1475_);
lean_ctor_set(v_reuseFailAlloc_1502_, 15, v_cFlags_1491_);
lean_ctor_set(v_reuseFailAlloc_1502_, 16, v_linkStaticFlags_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 17, v_linkSharedFlags_1493_);
lean_ctor_set(v_reuseFailAlloc_1502_, 18, v_ccFlags_1494_);
lean_ctor_set(v_reuseFailAlloc_1502_, 19, v_ccLinkStaticFlags_1495_);
lean_ctor_set(v_reuseFailAlloc_1502_, 20, v_ccLinkSharedFlags_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*21, v_customCc_1490_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1507_, lean_object* v_i_1508_){
_start:
{
lean_object* v_cc_1511_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1542_ = lean_io_getenv(v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 1)
{
lean_object* v_val_1543_; 
lean_dec_ref(v_sysroot_1507_);
v_val_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_cc_1511_ = v_val_1543_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
lean_dec(v___x_1542_);
lean_inc_ref(v_sysroot_1507_);
v___x_1544_ = l_Lake_leanCcExe(v_sysroot_1507_);
v___x_1545_ = l_System_FilePath_pathExists(v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v___x_1544_);
lean_dec_ref(v_sysroot_1507_);
v___x_1546_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1547_ = lean_io_getenv(v___x_1546_);
if (lean_obj_tag(v___x_1547_) == 1)
{
lean_object* v_val_1548_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_cc_1511_ = v_val_1548_;
goto v___jp_1510_;
}
else
{
lean_object* v_sysroot_1549_; lean_object* v_githash_1550_; lean_object* v_srcDir_1551_; lean_object* v_leanLibDir_1552_; lean_object* v_includeDir_1553_; lean_object* v_systemLibDir_1554_; lean_object* v_binDir_1555_; lean_object* v_lean_1556_; lean_object* v_leanir_1557_; lean_object* v_leanc_1558_; lean_object* v_leantar_1559_; lean_object* v_sharedDynlibs_1560_; lean_object* v_sharedDynlib_1561_; lean_object* v_ar_1562_; uint8_t v_customCc_1563_; lean_object* v_cFlags_1564_; lean_object* v_linkStaticFlags_1565_; lean_object* v_linkSharedFlags_1566_; lean_object* v_ccFlags_1567_; lean_object* v_ccLinkStaticFlags_1568_; lean_object* v_ccLinkSharedFlags_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v___x_1547_);
v_sysroot_1549_ = lean_ctor_get(v_i_1508_, 0);
v_githash_1550_ = lean_ctor_get(v_i_1508_, 1);
v_srcDir_1551_ = lean_ctor_get(v_i_1508_, 2);
v_leanLibDir_1552_ = lean_ctor_get(v_i_1508_, 3);
v_includeDir_1553_ = lean_ctor_get(v_i_1508_, 4);
v_systemLibDir_1554_ = lean_ctor_get(v_i_1508_, 5);
v_binDir_1555_ = lean_ctor_get(v_i_1508_, 6);
v_lean_1556_ = lean_ctor_get(v_i_1508_, 7);
v_leanir_1557_ = lean_ctor_get(v_i_1508_, 8);
v_leanc_1558_ = lean_ctor_get(v_i_1508_, 9);
v_leantar_1559_ = lean_ctor_get(v_i_1508_, 10);
v_sharedDynlibs_1560_ = lean_ctor_get(v_i_1508_, 11);
v_sharedDynlib_1561_ = lean_ctor_get(v_i_1508_, 12);
v_ar_1562_ = lean_ctor_get(v_i_1508_, 13);
v_customCc_1563_ = lean_ctor_get_uint8(v_i_1508_, sizeof(void*)*21);
v_cFlags_1564_ = lean_ctor_get(v_i_1508_, 15);
v_linkStaticFlags_1565_ = lean_ctor_get(v_i_1508_, 16);
v_linkSharedFlags_1566_ = lean_ctor_get(v_i_1508_, 17);
v_ccFlags_1567_ = lean_ctor_get(v_i_1508_, 18);
v_ccLinkStaticFlags_1568_ = lean_ctor_get(v_i_1508_, 19);
v_ccLinkSharedFlags_1569_ = lean_ctor_get(v_i_1508_, 20);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_i_1508_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_i_1508_, 14);
lean_dec(v_unused_1578_);
v___x_1571_ = v_i_1508_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1569_);
lean_inc(v_ccLinkStaticFlags_1568_);
lean_inc(v_ccFlags_1567_);
lean_inc(v_linkSharedFlags_1566_);
lean_inc(v_linkStaticFlags_1565_);
lean_inc(v_cFlags_1564_);
lean_inc(v_ar_1562_);
lean_inc(v_sharedDynlib_1561_);
lean_inc(v_sharedDynlibs_1560_);
lean_inc(v_leantar_1559_);
lean_inc(v_leanc_1558_);
lean_inc(v_leanir_1557_);
lean_inc(v_lean_1556_);
lean_inc(v_binDir_1555_);
lean_inc(v_systemLibDir_1554_);
lean_inc(v_includeDir_1553_);
lean_inc(v_leanLibDir_1552_);
lean_inc(v_srcDir_1551_);
lean_inc(v_githash_1550_);
lean_inc(v_sysroot_1549_);
lean_dec(v_i_1508_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 14, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_sysroot_1549_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_githash_1550_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_srcDir_1551_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_leanLibDir_1552_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_includeDir_1553_);
lean_ctor_set(v_reuseFailAlloc_1576_, 5, v_systemLibDir_1554_);
lean_ctor_set(v_reuseFailAlloc_1576_, 6, v_binDir_1555_);
lean_ctor_set(v_reuseFailAlloc_1576_, 7, v_lean_1556_);
lean_ctor_set(v_reuseFailAlloc_1576_, 8, v_leanir_1557_);
lean_ctor_set(v_reuseFailAlloc_1576_, 9, v_leanc_1558_);
lean_ctor_set(v_reuseFailAlloc_1576_, 10, v_leantar_1559_);
lean_ctor_set(v_reuseFailAlloc_1576_, 11, v_sharedDynlibs_1560_);
lean_ctor_set(v_reuseFailAlloc_1576_, 12, v_sharedDynlib_1561_);
lean_ctor_set(v_reuseFailAlloc_1576_, 13, v_ar_1562_);
lean_ctor_set(v_reuseFailAlloc_1576_, 14, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1576_, 15, v_cFlags_1564_);
lean_ctor_set(v_reuseFailAlloc_1576_, 16, v_linkStaticFlags_1565_);
lean_ctor_set(v_reuseFailAlloc_1576_, 17, v_linkSharedFlags_1566_);
lean_ctor_set(v_reuseFailAlloc_1576_, 18, v_ccFlags_1567_);
lean_ctor_set(v_reuseFailAlloc_1576_, 19, v_ccLinkStaticFlags_1568_);
lean_ctor_set(v_reuseFailAlloc_1576_, 20, v_ccLinkSharedFlags_1569_);
lean_ctor_set_uint8(v_reuseFailAlloc_1576_, sizeof(void*)*21, v_customCc_1563_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1507_, v_i_1508_, v___x_1544_);
lean_dec_ref(v_sysroot_1507_);
return v___x_1579_;
}
}
v___jp_1510_:
{
lean_object* v_sysroot_1512_; lean_object* v_githash_1513_; lean_object* v_srcDir_1514_; lean_object* v_leanLibDir_1515_; lean_object* v_includeDir_1516_; lean_object* v_systemLibDir_1517_; lean_object* v_binDir_1518_; lean_object* v_lean_1519_; lean_object* v_leanir_1520_; lean_object* v_leanc_1521_; lean_object* v_leantar_1522_; lean_object* v_sharedDynlibs_1523_; lean_object* v_sharedDynlib_1524_; lean_object* v_ar_1525_; uint8_t v_customCc_1526_; lean_object* v_cFlags_1527_; lean_object* v_linkStaticFlags_1528_; lean_object* v_linkSharedFlags_1529_; lean_object* v_ccFlags_1530_; lean_object* v_ccLinkStaticFlags_1531_; lean_object* v_ccLinkSharedFlags_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_sysroot_1512_ = lean_ctor_get(v_i_1508_, 0);
v_githash_1513_ = lean_ctor_get(v_i_1508_, 1);
v_srcDir_1514_ = lean_ctor_get(v_i_1508_, 2);
v_leanLibDir_1515_ = lean_ctor_get(v_i_1508_, 3);
v_includeDir_1516_ = lean_ctor_get(v_i_1508_, 4);
v_systemLibDir_1517_ = lean_ctor_get(v_i_1508_, 5);
v_binDir_1518_ = lean_ctor_get(v_i_1508_, 6);
v_lean_1519_ = lean_ctor_get(v_i_1508_, 7);
v_leanir_1520_ = lean_ctor_get(v_i_1508_, 8);
v_leanc_1521_ = lean_ctor_get(v_i_1508_, 9);
v_leantar_1522_ = lean_ctor_get(v_i_1508_, 10);
v_sharedDynlibs_1523_ = lean_ctor_get(v_i_1508_, 11);
v_sharedDynlib_1524_ = lean_ctor_get(v_i_1508_, 12);
v_ar_1525_ = lean_ctor_get(v_i_1508_, 13);
v_customCc_1526_ = lean_ctor_get_uint8(v_i_1508_, sizeof(void*)*21);
v_cFlags_1527_ = lean_ctor_get(v_i_1508_, 15);
v_linkStaticFlags_1528_ = lean_ctor_get(v_i_1508_, 16);
v_linkSharedFlags_1529_ = lean_ctor_get(v_i_1508_, 17);
v_ccFlags_1530_ = lean_ctor_get(v_i_1508_, 18);
v_ccLinkStaticFlags_1531_ = lean_ctor_get(v_i_1508_, 19);
v_ccLinkSharedFlags_1532_ = lean_ctor_get(v_i_1508_, 20);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_i_1508_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v_i_1508_, 14);
lean_dec(v_unused_1540_);
v___x_1534_ = v_i_1508_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1532_);
lean_inc(v_ccLinkStaticFlags_1531_);
lean_inc(v_ccFlags_1530_);
lean_inc(v_linkSharedFlags_1529_);
lean_inc(v_linkStaticFlags_1528_);
lean_inc(v_cFlags_1527_);
lean_inc(v_ar_1525_);
lean_inc(v_sharedDynlib_1524_);
lean_inc(v_sharedDynlibs_1523_);
lean_inc(v_leantar_1522_);
lean_inc(v_leanc_1521_);
lean_inc(v_leanir_1520_);
lean_inc(v_lean_1519_);
lean_inc(v_binDir_1518_);
lean_inc(v_systemLibDir_1517_);
lean_inc(v_includeDir_1516_);
lean_inc(v_leanLibDir_1515_);
lean_inc(v_srcDir_1514_);
lean_inc(v_githash_1513_);
lean_inc(v_sysroot_1512_);
lean_dec(v_i_1508_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 14, v_cc_1511_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_sysroot_1512_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_githash_1513_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_srcDir_1514_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_leanLibDir_1515_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_includeDir_1516_);
lean_ctor_set(v_reuseFailAlloc_1538_, 5, v_systemLibDir_1517_);
lean_ctor_set(v_reuseFailAlloc_1538_, 6, v_binDir_1518_);
lean_ctor_set(v_reuseFailAlloc_1538_, 7, v_lean_1519_);
lean_ctor_set(v_reuseFailAlloc_1538_, 8, v_leanir_1520_);
lean_ctor_set(v_reuseFailAlloc_1538_, 9, v_leanc_1521_);
lean_ctor_set(v_reuseFailAlloc_1538_, 10, v_leantar_1522_);
lean_ctor_set(v_reuseFailAlloc_1538_, 11, v_sharedDynlibs_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 12, v_sharedDynlib_1524_);
lean_ctor_set(v_reuseFailAlloc_1538_, 13, v_ar_1525_);
lean_ctor_set(v_reuseFailAlloc_1538_, 14, v_cc_1511_);
lean_ctor_set(v_reuseFailAlloc_1538_, 15, v_cFlags_1527_);
lean_ctor_set(v_reuseFailAlloc_1538_, 16, v_linkStaticFlags_1528_);
lean_ctor_set(v_reuseFailAlloc_1538_, 17, v_linkSharedFlags_1529_);
lean_ctor_set(v_reuseFailAlloc_1538_, 18, v_ccFlags_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 19, v_ccLinkStaticFlags_1531_);
lean_ctor_set(v_reuseFailAlloc_1538_, 20, v_ccLinkSharedFlags_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*21, v_customCc_1526_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1580_, lean_object* v_i_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1580_, v_i_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1584_, uint8_t v_collocated_1585_){
_start:
{
lean_object* v_githash_1588_; 
if (v_collocated_1585_ == 0)
{
lean_object* v___x_1614_; 
lean_inc_ref(v_sysroot_1584_);
v___x_1614_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1584_);
v_githash_1588_ = v___x_1614_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_githash;
v_githash_1588_ = v___x_1615_;
goto v___jp_1587_;
}
v___jp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_inc_ref_n(v_sysroot_1584_, 12);
v___x_1589_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1584_);
v___x_1590_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1591_ = l_System_FilePath_join(v_sysroot_1584_, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1593_ = l_System_FilePath_join(v___x_1591_, v___x_1592_);
v___x_1594_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1595_ = l_System_FilePath_join(v_sysroot_1584_, v___x_1594_);
lean_inc_ref(v___x_1595_);
v___x_1596_ = l_System_FilePath_join(v___x_1595_, v___x_1592_);
v___x_1597_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1598_ = l_System_FilePath_join(v_sysroot_1584_, v___x_1597_);
v___x_1599_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1600_ = l_System_FilePath_join(v_sysroot_1584_, v___x_1599_);
v___x_1601_ = l_Lake_leanExe(v_sysroot_1584_);
v___x_1602_ = l_Lake_leanirExe(v_sysroot_1584_);
v___x_1603_ = l_Lake_leancExe(v_sysroot_1584_);
v___x_1604_ = l_Lake_leantarExe(v_sysroot_1584_);
v___x_1605_ = l_Lake_leanSharedDynlibs(v_sysroot_1584_);
v___x_1606_ = l_Lake_leanSharedDynlib(v_sysroot_1584_);
v___x_1607_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1608_ = 1;
v___x_1609_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1610_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1611_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_1612_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1612_, 0, v_sysroot_1584_);
lean_ctor_set(v___x_1612_, 1, v_githash_1588_);
lean_ctor_set(v___x_1612_, 2, v___x_1593_);
lean_ctor_set(v___x_1612_, 3, v___x_1596_);
lean_ctor_set(v___x_1612_, 4, v___x_1598_);
lean_ctor_set(v___x_1612_, 5, v___x_1595_);
lean_ctor_set(v___x_1612_, 6, v___x_1600_);
lean_ctor_set(v___x_1612_, 7, v___x_1601_);
lean_ctor_set(v___x_1612_, 8, v___x_1602_);
lean_ctor_set(v___x_1612_, 9, v___x_1603_);
lean_ctor_set(v___x_1612_, 10, v___x_1604_);
lean_ctor_set(v___x_1612_, 11, v___x_1605_);
lean_ctor_set(v___x_1612_, 12, v___x_1606_);
lean_ctor_set(v___x_1612_, 13, v___x_1589_);
lean_ctor_set(v___x_1612_, 14, v___x_1607_);
lean_ctor_set(v___x_1612_, 15, v___x_1609_);
lean_ctor_set(v___x_1612_, 16, v___x_1610_);
lean_ctor_set(v___x_1612_, 17, v___x_1611_);
lean_ctor_set(v___x_1612_, 18, v___x_1609_);
lean_ctor_set(v___x_1612_, 19, v___x_1610_);
lean_ctor_set(v___x_1612_, 20, v___x_1611_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*21, v___x_1608_);
v___x_1613_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1584_, v___x_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1616_, lean_object* v_collocated_1617_, lean_object* v_a_1618_){
_start:
{
uint8_t v_collocated_boxed_1619_; lean_object* v_res_1620_; 
v_collocated_boxed_1619_ = lean_unbox(v_collocated_1617_);
v_res_1620_ = l_Lake_LeanInstall_get(v_sysroot_1616_, v_collocated_boxed_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lake_findLeanSysroot_x3f(v_lean_1621_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_box(0);
return v___x_1624_;
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1634_; 
v_val_1625_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1627_ = v___x_1623_;
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_dec(v___x_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1629_ = 0;
v___x_1630_ = l_Lake_LeanInstall_get(v_val_1625_, v___x_1629_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1630_);
v___x_1632_ = v___x_1627_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_io_app_path();
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1643_ = l_System_FilePath_parent(v_a_1642_);
if (lean_obj_tag(v___x_1643_) == 1)
{
lean_object* v_val_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_val_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc_n(v_val_1644_, 2);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1646_ = l_System_FilePath_join(v_val_1644_, v___x_1645_);
v___x_1647_ = l_System_FilePath_exeExtension;
v___x_1648_ = l_System_FilePath_addExtension(v___x_1646_, v___x_1647_);
v___x_1649_ = l_System_FilePath_pathExists(v___x_1648_);
lean_dec_ref(v___x_1648_);
if (v___x_1649_ == 0)
{
lean_dec(v_val_1644_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = l_System_FilePath_parent(v_val_1644_);
return v___x_1650_;
}
}
else
{
lean_dec(v___x_1643_);
goto v___jp_1639_;
}
}
else
{
lean_dec_ref_known(v___x_1641_, 1);
goto v___jp_1639_;
}
v___jp_1639_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_box(0);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_System_FilePath_parent(v_lake_1653_);
if (lean_obj_tag(v___x_1654_) == 0)
{
return v___x_1654_;
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1656_; 
v_val_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = l_System_FilePath_parent(v_val_1655_);
if (lean_obj_tag(v___x_1656_) == 0)
{
return v___x_1656_;
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1658_; 
v_val_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = l_System_FilePath_parent(v_val_1657_);
if (lean_obj_tag(v___x_1658_) == 0)
{
return v___x_1658_;
}
else
{
lean_object* v_val_1659_; lean_object* v___x_1660_; 
v_val_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_val_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = l_System_FilePath_parent(v_val_1659_);
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1662_){
_start:
{
lean_object* v___x_1664_; 
lean_inc_ref(v_lake_1662_);
v___x_1664_ = l_Lake_lakeBuildHome_x3f(v_lake_1662_);
if (lean_obj_tag(v___x_1664_) == 1)
{
lean_object* v_val_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1689_; 
v_val_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1689_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_val_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1689_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_lake_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1669_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1665_, 2);
v___x_1670_ = l_System_FilePath_join(v_val_1665_, v___x_1669_);
v___x_1671_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1670_);
v___x_1672_ = l_System_FilePath_join(v___x_1670_, v___x_1671_);
v___x_1673_ = l_Lake_defaultLeanLibDir;
v___x_1674_ = l_System_FilePath_join(v___x_1670_, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1676_ = 0;
v___x_1677_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref_n(v___x_1674_, 2);
v___x_1678_ = l_System_FilePath_join(v___x_1674_, v___x_1677_);
v___x_1679_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1680_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1675_);
lean_ctor_set(v___x_1680_, 2, v___x_1679_);
lean_ctor_set(v___x_1680_, 3, v___x_1679_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*4, v___x_1676_);
v_lake_1681_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1681_, 0, v_val_1665_);
lean_ctor_set(v_lake_1681_, 1, v_val_1665_);
lean_ctor_set(v_lake_1681_, 2, v___x_1672_);
lean_ctor_set(v_lake_1681_, 3, v___x_1674_);
lean_ctor_set(v_lake_1681_, 4, v___x_1680_);
lean_ctor_set(v_lake_1681_, 5, v_lake_1662_);
v___x_1682_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1683_ = l_System_FilePath_join(v___x_1674_, v___x_1682_);
v___x_1684_ = l_System_FilePath_pathExists(v___x_1683_);
lean_dec_ref(v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref_known(v_lake_1681_, 6);
lean_del_object(v___x_1667_);
v___x_1685_ = lean_box(0);
return v___x_1685_;
}
else
{
lean_object* v___x_1687_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v_lake_1681_);
v___x_1687_ = v___x_1667_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_lake_1681_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v___x_1690_; 
lean_dec(v___x_1664_);
lean_dec_ref(v_lake_1662_);
v___x_1690_ = lean_box(0);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lake_getLakeInstall_x3f(v_lake_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v_lean_1698_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1712_ = lean_io_getenv(v___x_1711_);
if (lean_obj_tag(v___x_1712_) == 1)
{
lean_object* v_val_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
v_val_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_val_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1717_ = 0;
v___x_1718_ = l_Lake_LeanInstall_get(v_val_1713_, v___x_1717_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v___x_1712_);
v___x_1723_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1724_ = lean_io_getenv(v___x_1723_);
if (lean_obj_tag(v___x_1724_) == 1)
{
lean_object* v_val_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v_startInclusive_1730_; lean_object* v_endExclusive_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_val_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_n(v_val_1725_, 2);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_string_utf8_byte_size(v_val_1725_);
v___x_1728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1728_, 0, v_val_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1726_);
lean_ctor_set(v___x_1728_, 2, v___x_1727_);
v___x_1729_ = l_String_Slice_trimAscii(v___x_1728_);
v_startInclusive_1730_ = lean_ctor_get(v___x_1729_, 1);
lean_inc(v_startInclusive_1730_);
v_endExclusive_1731_ = lean_ctor_get(v___x_1729_, 2);
lean_inc(v_endExclusive_1731_);
lean_dec_ref(v___x_1729_);
v___x_1732_ = lean_nat_sub(v_endExclusive_1731_, v_startInclusive_1730_);
lean_dec(v_startInclusive_1730_);
lean_dec(v_endExclusive_1731_);
v___x_1733_ = lean_nat_dec_eq(v___x_1732_, v___x_1726_);
lean_dec(v___x_1732_);
if (v___x_1733_ == 0)
{
v_lean_1698_ = v_val_1725_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1734_; 
lean_dec(v_val_1725_);
v___x_1734_ = lean_box(0);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1735_; 
lean_dec(v___x_1724_);
v___x_1735_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v_lean_1698_ = v___x_1735_;
goto v___jp_1697_;
}
}
v___jp_1697_:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lake_findLeanSysroot_x3f(v_lean_1698_);
if (lean_obj_tag(v___x_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1709_; 
v_val_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_val_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1704_ = 0;
v___x_1705_ = l_Lake_LeanInstall_get(v_val_1700_, v___x_1704_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1705_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v___x_1710_; 
lean_dec(v___x_1699_);
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lake_findLeanInstall_x3f();
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_io_app_path();
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = l_Lake_getLakeInstall_x3f(v_a_1768_);
if (lean_obj_tag(v___x_1769_) == 1)
{
return v___x_1769_;
}
else
{
lean_dec(v___x_1769_);
goto v___jp_1740_;
}
}
else
{
lean_dec_ref_known(v___x_1767_, 1);
goto v___jp_1740_;
}
v___jp_1740_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1742_ = lean_io_getenv(v___x_1741_);
if (lean_obj_tag(v___x_1742_) == 1)
{
lean_object* v_val_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1765_; 
v_val_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1765_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_val_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1765_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1747_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1743_, 2);
v___x_1748_ = l_System_FilePath_join(v_val_1743_, v___x_1747_);
v___x_1749_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1748_);
v___x_1750_ = l_System_FilePath_join(v___x_1748_, v___x_1749_);
v___x_1751_ = l_Lake_defaultLeanLibDir;
v___x_1752_ = l_System_FilePath_join(v___x_1748_, v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1754_ = 0;
v___x_1755_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref(v___x_1752_);
v___x_1756_ = l_System_FilePath_join(v___x_1752_, v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1758_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1753_);
lean_ctor_set(v___x_1758_, 2, v___x_1757_);
lean_ctor_set(v___x_1758_, 3, v___x_1757_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*4, v___x_1754_);
v___x_1759_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1750_);
v___x_1760_ = l_System_FilePath_join(v___x_1750_, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1761_, 0, v_val_1743_);
lean_ctor_set(v___x_1761_, 1, v_val_1743_);
lean_ctor_set(v___x_1761_, 2, v___x_1750_);
lean_ctor_set(v___x_1761_, 3, v___x_1752_);
lean_ctor_set(v___x_1761_, 4, v___x_1758_);
lean_ctor_set(v___x_1761_, 5, v___x_1760_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1761_);
v___x_1763_ = v___x_1745_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_object* v___x_1766_; 
lean_dec(v___x_1742_);
v___x_1766_ = lean_box(0);
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lake_findLakeInstall_x3f();
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = l_Lake_findElanInstall_x3f();
v___x_1775_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1775_) == 1)
{
lean_object* v_val_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1833_; 
v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1833_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_val_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1833_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1781_ = lean_io_getenv(v___x_1780_);
if (lean_obj_tag(v___x_1781_) == 0)
{
goto v___jp_1782_;
}
else
{
lean_object* v_val_1792_; lean_object* v___x_1793_; 
v_val_1792_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1793_ = l_Lake_envToBool_x3f(v_val_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
goto v___jp_1782_;
}
else
{
lean_object* v_val_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1832_; 
v_val_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1832_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_val_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1832_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_unbox(v_val_1794_);
if (v___x_1798_ == 0)
{
lean_del_object(v___x_1796_);
lean_dec(v_val_1794_);
goto v___jp_1782_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_del_object(v___x_1778_);
v___x_1799_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1800_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
lean_inc_n(v_val_1776_, 10);
v___x_1801_ = l_System_FilePath_join(v_val_1776_, v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1803_ = l_System_FilePath_join(v___x_1801_, v___x_1802_);
v___x_1804_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1805_ = l_System_FilePath_join(v_val_1776_, v___x_1804_);
lean_inc_ref(v___x_1805_);
v___x_1806_ = l_System_FilePath_join(v___x_1805_, v___x_1802_);
v___x_1807_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1808_ = l_System_FilePath_join(v_val_1776_, v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1810_ = l_System_FilePath_join(v_val_1776_, v___x_1809_);
v___x_1811_ = l_Lake_leanExe(v_val_1776_);
v___x_1812_ = l_Lake_leanirExe(v_val_1776_);
v___x_1813_ = l_Lake_leancExe(v_val_1776_);
v___x_1814_ = l_Lake_leantarExe(v_val_1776_);
v___x_1815_ = l_Lake_leanSharedDynlibs(v_val_1776_);
v___x_1816_ = l_Lake_leanSharedDynlib(v_val_1776_);
v___x_1817_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_1818_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1819_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1820_ = lean_unbox(v_val_1794_);
v___x_1821_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
lean_inc_ref(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1823_, 0, v_val_1776_);
lean_ctor_set(v___x_1823_, 1, v___x_1799_);
lean_ctor_set(v___x_1823_, 2, v___x_1803_);
lean_ctor_set(v___x_1823_, 3, v___x_1806_);
lean_ctor_set(v___x_1823_, 4, v___x_1808_);
lean_ctor_set(v___x_1823_, 5, v___x_1805_);
lean_ctor_set(v___x_1823_, 6, v___x_1810_);
lean_ctor_set(v___x_1823_, 7, v___x_1811_);
lean_ctor_set(v___x_1823_, 8, v___x_1812_);
lean_ctor_set(v___x_1823_, 9, v___x_1813_);
lean_ctor_set(v___x_1823_, 10, v___x_1814_);
lean_ctor_set(v___x_1823_, 11, v___x_1815_);
lean_ctor_set(v___x_1823_, 12, v___x_1816_);
lean_ctor_set(v___x_1823_, 13, v___x_1817_);
lean_ctor_set(v___x_1823_, 14, v___x_1818_);
lean_ctor_set(v___x_1823_, 15, v___x_1819_);
lean_ctor_set(v___x_1823_, 16, v___x_1821_);
lean_ctor_set(v___x_1823_, 17, v___x_1822_);
lean_ctor_set(v___x_1823_, 18, v___x_1819_);
lean_ctor_set(v___x_1823_, 19, v___x_1821_);
lean_ctor_set(v___x_1823_, 20, v___x_1822_);
v___x_1824_ = lean_unbox(v_val_1794_);
lean_dec(v_val_1794_);
lean_ctor_set_uint8(v___x_1823_, sizeof(void*)*21, v___x_1824_);
v___x_1825_ = l_Lake_LakeInstall_ofLean(v___x_1823_);
v___x_1826_ = l_Lake_findLeanInstall_x3f();
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1825_);
v___x_1828_ = v___x_1796_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1825_);
v___x_1828_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1826_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1774_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
return v___x_1830_;
}
}
}
}
}
v___jp_1782_:
{
uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1783_ = 1;
v___x_1784_ = l_Lake_LeanInstall_get(v_val_1776_, v___x_1783_);
lean_inc_ref(v___x_1784_);
v___x_1785_ = l_Lake_LakeInstall_ofLean(v___x_1784_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1784_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1784_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1785_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1774_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
return v___x_1790_;
}
}
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v___x_1775_);
v___x_1834_ = l_Lake_findLeanInstall_x3f();
v___x_1835_ = l_Lake_findLakeInstall_x3f();
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1774_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
return v___x_1837_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lake_findInstall_x3f();
return v_res_1839_;
}
}
lean_object* runtime_initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Compiler_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedElanInstall_default = _init_l_Lake_instInhabitedElanInstall_default();
lean_mark_persistent(l_Lake_instInhabitedElanInstall_default);
l_Lake_instInhabitedElanInstall = _init_l_Lake_instInhabitedElanInstall();
lean_mark_persistent(l_Lake_instInhabitedElanInstall);
l_Lake_leanSharedLib = _init_l_Lake_leanSharedLib();
lean_mark_persistent(l_Lake_leanSharedLib);
l_Lake_initSharedLib = _init_l_Lake_initSharedLib();
lean_mark_persistent(l_Lake_initSharedLib);
l_Lake_instInhabitedLeanInstall_default = _init_l_Lake_instInhabitedLeanInstall_default();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default);
l_Lake_instInhabitedLeanInstall = _init_l_Lake_instInhabitedLeanInstall();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall);
l_Lake_lakeExe = _init_l_Lake_lakeExe();
lean_mark_persistent(l_Lake_lakeExe);
l_Lake_instInhabitedLakeInstall_default = _init_l_Lake_instInhabitedLakeInstall_default();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall_default);
l_Lake_instInhabitedLakeInstall = _init_l_Lake_instInhabitedLakeInstall();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
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
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_InstallPath(builtin);
}
#ifdef __cplusplus
}
#endif
