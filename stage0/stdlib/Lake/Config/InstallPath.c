// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: public import Lean.Compiler.FFI public import Lake.Config.Dynlib public import Lake.Config.Defaults public import Lake.Util.NativeLib import Init.Data.String.Modify import Init.System.Platform
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lake_instReprDynlib_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedDynlib_default;
extern lean_object* l_System_instInhabitedFilePath_default;
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
extern lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBuildDir;
extern lean_object* l_Lake_defaultBinDir;
extern lean_object* l_Lake_defaultLeanLibDir;
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
static lean_once_cell_t l_Lake_instInhabitedElanInstall_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedElanInstall_default___closed__0;
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
static const lean_string_object l_Lake_toolchain2Dir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_toolchain2Dir___closed__0 = (const lean_object*)&l_Lake_toolchain2Dir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_leanExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lake_leanExe___closed__0 = (const lean_object*)&l_Lake_leanExe___closed__0_value;
static const lean_string_object l_Lake_leanExe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_leanExe___closed__1 = (const lean_object*)&l_Lake_leanExe___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object*);
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
static const lean_array_object l_Lake_instInhabitedLeanInstall_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprElanInstall_repr___redArg___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value;
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
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leanExe___closed__1_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leancExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__19;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leantarExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__20 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__20_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sharedLib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__21 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__21_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__22 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__23;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "initSharedLib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__24 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__24_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__24_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__25 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__25_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ar"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__26 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__26_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__27 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__27_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__28;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "cc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__29 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__29_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__29_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__30 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "customCc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__31 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__31_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__32 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__32_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__33;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__34 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__34_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__34_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__35 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__36 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__36_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__36_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__37 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__37_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__38;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__39 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__39_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__39_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ccFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__43 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__43_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__43_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__44 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__44_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__45;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__46 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__46_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__46_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__47 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__47_value;
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLeanInstall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLeanInstall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLeanInstall___closed__0 = (const lean_object*)&l_Lake_instReprLeanInstall___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLeanInstall = (const lean_object*)&l_Lake_instReprLeanInstall___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall;
static const lean_string_object l_Lake_instReprLakeInstall_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "libDir"};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__1_value;
static const lean_string_object l_Lake_instReprLakeInstall_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sharedDynlib"};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lake_instReprLakeInstall_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_lakeExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLakeInstall_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprLakeInstall_repr___redArg___closed__4_value;
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
static const lean_array_object l_Lake_LakeInstall_ofLean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__1 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__1_value;
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libLake_shared."};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__2 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__2_value;
static lean_once_cell_t l_Lake_LakeInstall_ofLean___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeInstall_ofLean___closed__3;
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object*);
static const lean_string_object l_Lake_findElanInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ELAN_HOME"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__0 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__0_value;
static const lean_string_object l_Lake_findElanInstall_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ELAN"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__1 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__1_value;
static const lean_string_object l_Lake_findElanInstall_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toolchains"};
static const lean_object* l_Lake_findElanInstall_x3f___closed__2 = (const lean_object*)&l_Lake_findElanInstall_x3f___closed__2_value;
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
static const lean_string_object l_Lake_LeanInstall_get___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* l_Lake_LeanInstall_get___closed__0 = (const lean_object*)&l_Lake_LeanInstall_get___closed__0_value;
static const lean_string_object l_Lake_LeanInstall_get___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l_Lake_LeanInstall_get___closed__1 = (const lean_object*)&l_Lake_LeanInstall_get___closed__1_value;
static const lean_string_object l_Lake_LeanInstall_get___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "-Wno-unused-command-line-argument"};
static const lean_object* l_Lake_LeanInstall_get___closed__2 = (const lean_object*)&l_Lake_LeanInstall_get___closed__2_value;
static lean_once_cell_t l_Lake_LeanInstall_get___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanInstall_get___closed__3;
static lean_once_cell_t l_Lake_LeanInstall_get___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanInstall_get___closed__4;
static lean_once_cell_t l_Lake_LeanInstall_get___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanInstall_get___closed__5;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f();
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object*);
static const lean_string_object l_Lake_getLakeInstall_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_getLakeInstall_x3f___closed__0 = (const lean_object*)&l_Lake_getLakeInstall_x3f___closed__0_value;
static lean_once_cell_t l_Lake_getLakeInstall_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_getLakeInstall_x3f___closed__1;
static const lean_string_object l_Lake_getLakeInstall_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lake.olean"};
static const lean_object* l_Lake_getLakeInstall_x3f___closed__2 = (const lean_object*)&l_Lake_getLakeInstall_x3f___closed__2_value;
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
uint32_t v___y_15_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_string_utf8_byte_size(v_s_12_);
v___x_21_ = lean_nat_dec_eq(v_p_13_, v___x_20_);
if (v___x_21_ == 0)
{
uint32_t v___x_22_; uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_string_utf8_get_fast(v_s_12_, v_p_13_);
v___x_23_ = 65;
v___x_24_ = lean_uint32_dec_le(v___x_23_, v___x_22_);
if (v___x_24_ == 0)
{
v___y_15_ = v___x_22_;
goto v___jp_14_;
}
else
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 90;
v___x_26_ = lean_uint32_dec_le(v___x_22_, v___x_25_);
if (v___x_26_ == 0)
{
v___y_15_ = v___x_22_;
goto v___jp_14_;
}
else
{
uint32_t v___x_27_; uint32_t v___x_28_; 
v___x_27_ = 32;
v___x_28_ = lean_uint32_add(v___x_22_, v___x_27_);
v___y_15_ = v___x_28_;
goto v___jp_14_;
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
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc(v_p_13_);
v___x_16_ = lean_string_utf8_set(v_s_12_, v_p_13_, v___y_15_);
v___x_17_ = l_Char_utf8Size(v___y_15_);
v___x_18_ = lean_nat_add(v_p_13_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v_p_13_);
v_s_12_ = v___x_16_;
v_p_13_ = v___x_18_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* v_o_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_78_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__11));
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_77_, v___x_79_);
v___x_81_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_80_, v___x_78_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__23));
v___x_83_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_80_, v___x_82_);
lean_dec_ref(v___x_80_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box(v___x_81_);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec_ref(v___x_80_);
v___x_87_ = lean_box(v___x_81_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__0(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = l_System_instInhabitedFilePath_default;
v___x_90_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
lean_ctor_set(v___x_90_, 2, v___x_89_);
lean_ctor_set(v___x_90_, 3, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__0, &l_Lake_instInhabitedElanInstall_default___closed__0_once, _init_l_Lake_instInhabitedElanInstall_default___closed__0);
return v___x_91_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lake_instInhabitedElanInstall_default;
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_nat_to_int(v_a_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(8u);
v___x_109_ = lean_nat_to_int(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(10u);
v___x_123_ = lean_nat_to_int(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(17u);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__0));
v___x_131_ = lean_string_length(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__21, &l_Lake_instReprElanInstall_repr___redArg___closed__21_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__21);
v___x_133_ = lean_nat_to_int(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* v_x_138_){
_start:
{
lean_object* v_home_139_; lean_object* v_elan_140_; lean_object* v_binDir_141_; lean_object* v_toolchainsDir_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_home_139_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_home_139_);
v_elan_140_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_elan_140_);
v_binDir_141_ = lean_ctor_get(v_x_138_, 2);
lean_inc_ref(v_binDir_141_);
v_toolchainsDir_142_ = lean_ctor_get(v_x_138_, 3);
lean_inc_ref(v_toolchainsDir_142_);
lean_dec_ref(v_x_138_);
v___x_143_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_144_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_145_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_148_ = l_String_quote(v_home_139_);
v___x_149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_147_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Repr_addAppParen(v___x_150_, v___x_146_);
v___x_152_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_145_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_144_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_box(1);
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__13));
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_143_);
v___x_163_ = l_String_quote(v_elan_140_);
v___x_164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_147_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Repr_addAppParen(v___x_165_, v___x_146_);
v___x_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_145_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_153_);
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_162_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_156_);
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_158_);
v___x_172_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_143_);
v___x_175_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_176_ = l_String_quote(v_binDir_141_);
v___x_177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_147_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Repr_addAppParen(v___x_178_, v___x_146_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_153_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_174_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_156_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_158_);
v___x_185_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__18));
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_143_);
v___x_188_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_189_ = l_String_quote(v_toolchainsDir_142_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_147_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = l_Repr_addAppParen(v___x_191_, v___x_146_);
v___x_193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_188_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_153_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_187_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_197_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_195_);
v___x_199_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_196_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*1, v___x_153_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* v_x_203_, lean_object* v_prec_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lake_instReprElanInstall_repr___redArg(v_x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* v_x_206_, lean_object* v_prec_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lake_instReprElanInstall_repr(v_x_206_, v_prec_207_);
lean_dec(v_prec_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* v_toolchain_213_, lean_object* v_acc_214_, lean_object* v_pos_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_string_utf8_at_end(v_toolchain_213_, v_pos_215_);
if (v___x_216_ == 0)
{
uint32_t v_c_217_; lean_object* v_pos_x27_218_; uint32_t v___x_219_; uint8_t v___x_220_; 
v_c_217_ = lean_string_utf8_get_fast(v_toolchain_213_, v_pos_215_);
v_pos_x27_218_ = lean_string_utf8_next_fast(v_toolchain_213_, v_pos_215_);
lean_dec(v_pos_215_);
v___x_219_ = 47;
v___x_220_ = lean_uint32_dec_eq(v_c_217_, v___x_219_);
if (v___x_220_ == 0)
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 58;
v___x_222_ = lean_uint32_dec_eq(v_c_217_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_string_push(v_acc_214_, v_c_217_);
v_acc_214_ = v___x_223_;
v_pos_215_ = v_pos_x27_218_;
goto _start;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0));
v___x_226_ = lean_string_append(v_acc_214_, v___x_225_);
v_acc_214_ = v___x_226_;
v_pos_215_ = v_pos_x27_218_;
goto _start;
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1));
v___x_229_ = lean_string_append(v_acc_214_, v___x_228_);
v_acc_214_ = v___x_229_;
v_pos_215_ = v_pos_x27_218_;
goto _start;
}
}
else
{
lean_dec(v_pos_215_);
return v_acc_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* v_toolchain_231_, lean_object* v_acc_232_, lean_object* v_pos_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_231_, v_acc_232_, v_pos_233_);
lean_dec_ref(v_toolchain_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* v_toolchain_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* v_toolchain_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_toolchain2Dir(v_toolchain_240_);
lean_dec_ref(v_toolchain_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* v_toolchain_242_, lean_object* v_elan_243_){
_start:
{
lean_object* v_toolchainsDir_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_toolchainsDir_244_ = lean_ctor_get(v_elan_243_, 3);
lean_inc_ref(v_toolchainsDir_244_);
lean_dec_ref(v_elan_243_);
v___x_245_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_242_, v___x_245_, v___x_246_);
v___x_248_ = l_System_FilePath_join(v_toolchainsDir_244_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* v_toolchain_249_, lean_object* v_elan_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_249_, v_elan_250_);
lean_dec_ref(v_toolchain_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* v_sysroot_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_256_ = l_System_FilePath_join(v_sysroot_254_, v___x_255_);
v___x_257_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_258_ = l_System_FilePath_join(v___x_256_, v___x_257_);
v___x_259_ = l_System_FilePath_exeExtension;
v___x_260_ = l_System_FilePath_addExtension(v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_264_ = l_System_FilePath_join(v_sysroot_262_, v___x_263_);
v___x_265_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_266_ = l_System_FilePath_join(v___x_264_, v___x_265_);
v___x_267_ = l_System_FilePath_exeExtension;
v___x_268_ = l_System_FilePath_addExtension(v___x_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_271_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_272_ = l_System_FilePath_join(v_sysroot_270_, v___x_271_);
v___x_273_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_274_ = l_System_FilePath_join(v___x_272_, v___x_273_);
v___x_275_ = l_System_FilePath_exeExtension;
v___x_276_ = l_System_FilePath_addExtension(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_280_ = l_System_FilePath_join(v_sysroot_278_, v___x_279_);
v___x_281_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_282_ = l_System_FilePath_join(v___x_280_, v___x_281_);
v___x_283_ = l_System_FilePath_exeExtension;
v___x_284_ = l_System_FilePath_addExtension(v___x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_288_ = l_System_FilePath_join(v_sysroot_286_, v___x_287_);
v___x_289_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_290_ = l_System_FilePath_join(v___x_288_, v___x_289_);
v___x_291_ = l_System_FilePath_exeExtension;
v___x_292_ = l_System_FilePath_addExtension(v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_System_Platform_isWindows;
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_297_ = l_System_FilePath_join(v_sysroot_294_, v___x_296_);
v___x_298_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_299_ = l_System_FilePath_join(v___x_297_, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_301_ = l_System_FilePath_join(v_sysroot_294_, v___x_300_);
return v___x_301_;
}
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = l_Lake_sharedLibExt;
v___x_304_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_305_ = l_System_FilePath_addExtension(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_306_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = l_Lake_sharedLibExt;
v___x_309_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_310_ = l_System_FilePath_addExtension(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_311_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_315_ = 0;
v___x_316_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
v___x_317_ = l_System_instInhabitedFilePath_default;
v___x_318_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set(v___x_318_, 3, v___x_317_);
lean_ctor_set(v___x_318_, 4, v___x_317_);
lean_ctor_set(v___x_318_, 5, v___x_317_);
lean_ctor_set(v___x_318_, 6, v___x_317_);
lean_ctor_set(v___x_318_, 7, v___x_317_);
lean_ctor_set(v___x_318_, 8, v___x_317_);
lean_ctor_set(v___x_318_, 9, v___x_317_);
lean_ctor_set(v___x_318_, 10, v___x_317_);
lean_ctor_set(v___x_318_, 11, v___x_317_);
lean_ctor_set(v___x_318_, 12, v___x_317_);
lean_ctor_set(v___x_318_, 13, v___x_317_);
lean_ctor_set(v___x_318_, 14, v___x_314_);
lean_ctor_set(v___x_318_, 15, v___x_314_);
lean_ctor_set(v___x_318_, 16, v___x_314_);
lean_ctor_set(v___x_318_, 17, v___x_314_);
lean_ctor_set(v___x_318_, 18, v___x_314_);
lean_ctor_set(v___x_318_, 19, v___x_314_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*20, v___x_315_);
return v___x_318_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object* v___y_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_String_quote(v___y_321_);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_dec(v_x_324_);
return v_x_325_;
}
else
{
lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_339_; 
v_head_327_ = lean_ctor_get(v_x_326_, 0);
v_tail_328_ = lean_ctor_get(v_x_326_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_339_ == 0)
{
v___x_330_ = v_x_326_;
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_tail_328_);
lean_inc(v_head_327_);
lean_dec(v_x_326_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
lean_inc(v_x_324_);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 5);
lean_ctor_set(v___x_330_, 1, v_x_324_);
lean_ctor_set(v___x_330_, 0, v_x_325_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_x_325_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_x_324_);
v___x_333_ = v_reuseFailAlloc_338_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = l_String_quote(v_head_327_);
v___x_335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_333_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v_x_325_ = v___x_336_;
v_x_326_ = v_tail_328_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_dec(v_x_340_);
return v_x_341_;
}
else
{
lean_object* v_head_343_; lean_object* v_tail_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_355_; 
v_head_343_ = lean_ctor_get(v_x_342_, 0);
v_tail_344_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_355_ == 0)
{
v___x_346_ = v_x_342_;
v_isShared_347_ = v_isSharedCheck_355_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_tail_344_);
lean_inc(v_head_343_);
lean_dec(v_x_342_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_355_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
lean_inc(v_x_340_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 5);
lean_ctor_set(v___x_346_, 1, v_x_340_);
lean_ctor_set(v___x_346_, 0, v_x_341_);
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_x_341_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_x_340_);
v___x_349_ = v_reuseFailAlloc_354_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = l_String_quote(v_head_343_);
v___x_351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(v_x_340_, v___x_352_, v_tail_344_);
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_object* v___x_358_; 
lean_dec(v_x_357_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v_tail_359_; 
v_tail_359_ = lean_ctor_get(v_x_356_, 1);
if (lean_obj_tag(v_tail_359_) == 0)
{
lean_object* v_head_360_; lean_object* v___x_361_; 
lean_dec(v_x_357_);
v_head_360_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_head_360_);
lean_dec_ref(v_x_356_);
v___x_361_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_360_);
return v___x_361_;
}
else
{
lean_object* v_head_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_inc(v_tail_359_);
v_head_362_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_head_362_);
lean_dec_ref(v_x_356_);
v___x_363_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_362_);
v___x_364_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_357_, v___x_363_, v_tail_359_);
return v___x_364_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0));
v___x_371_ = lean_string_length(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3);
v___x_373_ = lean_nat_to_int(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_array_get_size(v_xs_381_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_nat_dec_eq(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_385_ = lean_array_to_list(v_xs_381_);
v___x_386_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1));
v___x_387_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_385_, v___x_386_);
v___x_388_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4);
v___x_389_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5));
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_387_);
v___x_391_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6));
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_388_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = l_Std_Format_fill(v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; 
lean_dec_ref(v_xs_381_);
v___x_395_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8));
return v___x_395_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_unsigned_to_nat(11u);
v___x_406_ = lean_nat_to_int(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(14u);
v___x_417_ = lean_nat_to_int(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(16u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(9u);
v___x_431_ = lean_nat_to_int(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(13u);
v___x_438_ = lean_nat_to_int(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(6u);
v___x_446_ = lean_nat_to_int(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__33(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(12u);
v___x_454_ = lean_nat_to_int(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__38(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_unsigned_to_nat(19u);
v___x_462_ = lean_nat_to_int(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__45(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(21u);
v___x_473_ = lean_nat_to_int(v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_477_){
_start:
{
lean_object* v_sysroot_478_; lean_object* v_githash_479_; lean_object* v_srcDir_480_; lean_object* v_leanLibDir_481_; lean_object* v_includeDir_482_; lean_object* v_systemLibDir_483_; lean_object* v_binDir_484_; lean_object* v_lean_485_; lean_object* v_leanc_486_; lean_object* v_leantar_487_; lean_object* v_sharedLib_488_; lean_object* v_initSharedLib_489_; lean_object* v_ar_490_; lean_object* v_cc_491_; uint8_t v_customCc_492_; lean_object* v_cFlags_493_; lean_object* v_linkStaticFlags_494_; lean_object* v_linkSharedFlags_495_; lean_object* v_ccFlags_496_; lean_object* v_ccLinkStaticFlags_497_; lean_object* v_ccLinkSharedFlags_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_sysroot_478_ = lean_ctor_get(v_x_477_, 0);
lean_inc_ref(v_sysroot_478_);
v_githash_479_ = lean_ctor_get(v_x_477_, 1);
lean_inc_ref(v_githash_479_);
v_srcDir_480_ = lean_ctor_get(v_x_477_, 2);
lean_inc_ref(v_srcDir_480_);
v_leanLibDir_481_ = lean_ctor_get(v_x_477_, 3);
lean_inc_ref(v_leanLibDir_481_);
v_includeDir_482_ = lean_ctor_get(v_x_477_, 4);
lean_inc_ref(v_includeDir_482_);
v_systemLibDir_483_ = lean_ctor_get(v_x_477_, 5);
lean_inc_ref(v_systemLibDir_483_);
v_binDir_484_ = lean_ctor_get(v_x_477_, 6);
lean_inc_ref(v_binDir_484_);
v_lean_485_ = lean_ctor_get(v_x_477_, 7);
lean_inc_ref(v_lean_485_);
v_leanc_486_ = lean_ctor_get(v_x_477_, 8);
lean_inc_ref(v_leanc_486_);
v_leantar_487_ = lean_ctor_get(v_x_477_, 9);
lean_inc_ref(v_leantar_487_);
v_sharedLib_488_ = lean_ctor_get(v_x_477_, 10);
lean_inc_ref(v_sharedLib_488_);
v_initSharedLib_489_ = lean_ctor_get(v_x_477_, 11);
lean_inc_ref(v_initSharedLib_489_);
v_ar_490_ = lean_ctor_get(v_x_477_, 12);
lean_inc_ref(v_ar_490_);
v_cc_491_ = lean_ctor_get(v_x_477_, 13);
lean_inc_ref(v_cc_491_);
v_customCc_492_ = lean_ctor_get_uint8(v_x_477_, sizeof(void*)*20);
v_cFlags_493_ = lean_ctor_get(v_x_477_, 14);
lean_inc_ref(v_cFlags_493_);
v_linkStaticFlags_494_ = lean_ctor_get(v_x_477_, 15);
lean_inc_ref(v_linkStaticFlags_494_);
v_linkSharedFlags_495_ = lean_ctor_get(v_x_477_, 16);
lean_inc_ref(v_linkSharedFlags_495_);
v_ccFlags_496_ = lean_ctor_get(v_x_477_, 17);
lean_inc_ref(v_ccFlags_496_);
v_ccLinkStaticFlags_497_ = lean_ctor_get(v_x_477_, 18);
lean_inc_ref(v_ccLinkStaticFlags_497_);
v_ccLinkSharedFlags_498_ = lean_ctor_get(v_x_477_, 19);
lean_inc_ref(v_ccLinkSharedFlags_498_);
lean_dec_ref(v_x_477_);
v___x_499_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_500_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_501_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_504_ = l_String_quote(v_sysroot_478_);
v___x_505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_503_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Repr_addAppParen(v___x_506_, v___x_502_);
v___x_508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_501_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = 0;
v___x_510_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1, v___x_509_);
v___x_511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_500_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_box(1);
v___x_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_499_);
v___x_519_ = l_String_quote(v_githash_479_);
v___x_520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___x_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_501_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_509_);
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_518_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v___x_512_);
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_514_);
v___x_526_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_499_);
v___x_529_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_530_ = l_String_quote(v_srcDir_480_);
v___x_531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_503_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Repr_addAppParen(v___x_532_, v___x_502_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_529_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_509_);
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_528_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_512_);
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_514_);
v___x_539_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_499_);
v___x_542_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_543_ = l_String_quote(v_leanLibDir_481_);
v___x_544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_503_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Repr_addAppParen(v___x_545_, v___x_502_);
v___x_547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_542_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*1, v___x_509_);
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_541_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_512_);
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_514_);
v___x_552_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_499_);
v___x_555_ = l_String_quote(v_includeDir_482_);
v___x_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_503_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Repr_addAppParen(v___x_557_, v___x_502_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_542_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*1, v___x_509_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_554_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_512_);
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_514_);
v___x_564_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_499_);
v___x_567_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_568_ = l_String_quote(v_systemLibDir_483_);
v___x_569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_503_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Repr_addAppParen(v___x_570_, v___x_502_);
v___x_572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_567_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*1, v___x_509_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_566_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_512_);
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_514_);
v___x_577_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_499_);
v___x_580_ = l_String_quote(v_binDir_484_);
v___x_581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_503_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Repr_addAppParen(v___x_582_, v___x_502_);
v___x_584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_529_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*1, v___x_509_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_579_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_512_);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_514_);
v___x_589_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_499_);
v___x_592_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_593_ = l_String_quote(v_lean_485_);
v___x_594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_503_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Repr_addAppParen(v___x_595_, v___x_502_);
v___x_597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_592_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*1, v___x_509_);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_591_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_512_);
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_514_);
v___x_602_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_499_);
v___x_605_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__19, &l_Lake_instReprLeanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__19);
v___x_606_ = l_String_quote(v_leanc_486_);
v___x_607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_503_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = l_Repr_addAppParen(v___x_608_, v___x_502_);
v___x_610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_605_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*1, v___x_509_);
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_604_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_512_);
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_514_);
v___x_615_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__20));
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_499_);
v___x_618_ = l_String_quote(v_leantar_487_);
v___x_619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_503_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l_Repr_addAppParen(v___x_620_, v___x_502_);
v___x_622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_501_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*1, v___x_509_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_617_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_512_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_514_);
v___x_627_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__22));
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_499_);
v___x_630_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__23, &l_Lake_instReprLeanInstall_repr___redArg___closed__23_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__23);
v___x_631_ = l_String_quote(v_sharedLib_488_);
v___x_632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_503_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Repr_addAppParen(v___x_633_, v___x_502_);
v___x_635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_630_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*1, v___x_509_);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_629_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_512_);
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_514_);
v___x_640_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_499_);
v___x_643_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_644_ = l_String_quote(v_initSharedLib_489_);
v___x_645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
v___x_646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_503_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Repr_addAppParen(v___x_646_, v___x_502_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_643_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_509_);
v___x_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_642_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_512_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_514_);
v___x_653_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__27));
v___x_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_499_);
v___x_656_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__28, &l_Lake_instReprLeanInstall_repr___redArg___closed__28_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28);
v___x_657_ = l_String_quote(v_ar_490_);
v___x_658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_503_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Repr_addAppParen(v___x_659_, v___x_502_);
v___x_661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_656_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*1, v___x_509_);
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_655_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_512_);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_514_);
v___x_666_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_499_);
v___x_669_ = l_String_quote(v_cc_491_);
v___x_670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_503_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Repr_addAppParen(v___x_671_, v___x_502_);
v___x_673_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_656_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*1, v___x_509_);
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_668_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_512_);
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_514_);
v___x_678_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__32));
v___x_679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_499_);
v___x_681_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__33, &l_Lake_instReprLeanInstall_repr___redArg___closed__33_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__33);
v___x_682_ = l_Bool_repr___redArg(v_customCc_492_);
v___x_683_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*1, v___x_509_);
v___x_685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_680_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_512_);
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_514_);
v___x_688_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__35));
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___x_499_);
v___x_691_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_cFlags_493_);
v___x_692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_529_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*1, v___x_509_);
v___x_694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_690_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_512_);
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_514_);
v___x_697_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__37));
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_499_);
v___x_700_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__38, &l_Lake_instReprLeanInstall_repr___redArg___closed__38_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__38);
v___x_701_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkStaticFlags_494_);
v___x_702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v___x_509_);
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_699_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_512_);
v___x_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_514_);
v___x_707_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__40));
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_499_);
v___x_710_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkSharedFlags_495_);
v___x_711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_700_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*1, v___x_509_);
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_709_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_512_);
v___x_715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_514_);
v___x_716_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__42));
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_499_);
v___x_719_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccFlags_496_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_501_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*1, v___x_509_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_718_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_512_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_514_);
v___x_725_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__44));
v___x_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_499_);
v___x_728_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__45, &l_Lake_instReprLeanInstall_repr___redArg___closed__45_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__45);
v___x_729_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkStaticFlags_497_);
v___x_730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_509_);
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_727_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_512_);
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_514_);
v___x_735_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__47));
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_499_);
v___x_738_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkSharedFlags_498_);
v___x_739_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_728_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_509_);
v___x_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_737_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_743_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_741_);
v___x_745_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_742_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*1, v___x_509_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_749_, lean_object* v_prec_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_752_, lean_object* v_prec_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lake_instReprLeanInstall_repr(v_x_752_, v_prec_753_);
lean_dec(v_prec_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = l_System_Platform_isWindows;
if (v___x_758_ == 0)
{
lean_object* v_leanLibDir_759_; lean_object* v_systemLibDir_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_leanLibDir_759_ = lean_ctor_get(v_self_757_, 3);
v_systemLibDir_760_ = lean_ctor_get(v_self_757_, 5);
v___x_761_ = lean_box(0);
lean_inc_ref(v_systemLibDir_760_);
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v_systemLibDir_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
lean_inc_ref(v_leanLibDir_759_);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v_leanLibDir_759_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
return v___x_763_;
}
else
{
lean_object* v_binDir_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_binDir_764_ = lean_ctor_get(v_self_757_, 6);
v___x_765_ = lean_box(0);
lean_inc_ref(v_binDir_764_);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v_binDir_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lake_LeanInstall_sharedLibPath(v_self_767_);
lean_dec_ref(v_self_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_769_){
_start:
{
uint8_t v_customCc_770_; 
v_customCc_770_ = lean_ctor_get_uint8(v_self_769_, sizeof(void*)*20);
if (v_customCc_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_box(0);
return v___x_771_;
}
else
{
lean_object* v_cc_772_; lean_object* v___x_773_; 
v_cc_772_ = lean_ctor_get(v_self_769_, 13);
lean_inc_ref(v_cc_772_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v_cc_772_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lake_LeanInstall_leanCc_x3f(v_self_774_);
lean_dec_ref(v_self_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_776_, lean_object* v_self_777_){
_start:
{
if (v_shared_776_ == 0)
{
lean_object* v_ccLinkStaticFlags_778_; 
v_ccLinkStaticFlags_778_ = lean_ctor_get(v_self_777_, 18);
lean_inc_ref(v_ccLinkStaticFlags_778_);
return v_ccLinkStaticFlags_778_;
}
else
{
lean_object* v_ccLinkSharedFlags_779_; 
v_ccLinkSharedFlags_779_ = lean_ctor_get(v_self_777_, 19);
lean_inc_ref(v_ccLinkSharedFlags_779_);
return v_ccLinkSharedFlags_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_780_, lean_object* v_self_781_){
_start:
{
uint8_t v_shared_boxed_782_; lean_object* v_res_783_; 
v_shared_boxed_782_ = lean_unbox(v_shared_780_);
v_res_783_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_782_, v_self_781_);
lean_dec_ref(v_self_781_);
return v_res_783_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = l_System_FilePath_exeExtension;
v___x_786_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_787_ = l_System_FilePath_addExtension(v___x_786_, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_788_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = l_Lake_instInhabitedDynlib_default;
v___x_790_ = l_System_instInhabitedFilePath_default;
v___x_791_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
lean_ctor_set(v___x_791_, 3, v___x_790_);
lean_ctor_set(v___x_791_, 4, v___x_789_);
lean_ctor_set(v___x_791_, 5, v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
return v___x_792_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_802_){
_start:
{
lean_object* v_home_803_; lean_object* v_srcDir_804_; lean_object* v_binDir_805_; lean_object* v_libDir_806_; lean_object* v_sharedDynlib_807_; lean_object* v_lake_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_home_803_ = lean_ctor_get(v_x_802_, 0);
lean_inc_ref(v_home_803_);
v_srcDir_804_ = lean_ctor_get(v_x_802_, 1);
lean_inc_ref(v_srcDir_804_);
v_binDir_805_ = lean_ctor_get(v_x_802_, 2);
lean_inc_ref(v_binDir_805_);
v_libDir_806_ = lean_ctor_get(v_x_802_, 3);
lean_inc_ref(v_libDir_806_);
v_sharedDynlib_807_ = lean_ctor_get(v_x_802_, 4);
lean_inc_ref(v_sharedDynlib_807_);
v_lake_808_ = lean_ctor_get(v_x_802_, 5);
lean_inc_ref(v_lake_808_);
lean_dec_ref(v_x_802_);
v___x_809_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_810_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_811_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_814_ = l_String_quote(v_home_803_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Repr_addAppParen(v___x_816_, v___x_812_);
v___x_818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_811_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = 0;
v___x_820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_819_);
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_810_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_box(1);
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_809_);
v___x_829_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_830_ = l_String_quote(v_srcDir_804_);
v___x_831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_813_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Repr_addAppParen(v___x_832_, v___x_812_);
v___x_834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_829_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*1, v___x_819_);
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_828_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_822_);
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_824_);
v___x_839_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___x_809_);
v___x_842_ = l_String_quote(v_binDir_805_);
v___x_843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_813_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Repr_addAppParen(v___x_844_, v___x_812_);
v___x_846_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_829_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*1, v___x_819_);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_841_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_822_);
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_824_);
v___x_851_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_809_);
v___x_854_ = l_String_quote(v_libDir_806_);
v___x_855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
v___x_856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_813_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Repr_addAppParen(v___x_856_, v___x_812_);
v___x_858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_829_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*1, v___x_819_);
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_853_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_822_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_824_);
v___x_863_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__3));
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_809_);
v___x_866_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_867_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_807_);
v___x_868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v___x_819_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_865_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_822_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_824_);
v___x_873_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__4));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_809_);
v___x_876_ = l_String_quote(v_lake_808_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
v___x_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_813_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Repr_addAppParen(v___x_878_, v___x_812_);
v___x_880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_811_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_819_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_875_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_884_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_882_);
v___x_886_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_883_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*1, v___x_819_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_890_, lean_object* v_prec_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_893_, lean_object* v_prec_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lake_instReprLakeInstall_repr(v_x_893_, v_prec_894_);
lean_dec(v_prec_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_898_){
_start:
{
lean_object* v_sharedDynlib_899_; lean_object* v_path_900_; 
v_sharedDynlib_899_ = lean_ctor_get(v_self_898_, 4);
v_path_900_ = lean_ctor_get(v_sharedDynlib_899_, 0);
lean_inc_ref(v_path_900_);
return v_path_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lake_LakeInstall_sharedLib(v_self_901_);
lean_dec_ref(v_self_901_);
return v_res_902_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__3(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_lib_909_; 
v___x_907_ = l_Lake_sharedLibExt;
v___x_908_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__2));
v_lib_909_ = lean_string_append(v___x_908_, v___x_907_);
return v_lib_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_910_){
_start:
{
lean_object* v_sysroot_911_; lean_object* v_srcDir_912_; lean_object* v_leanLibDir_913_; lean_object* v_binDir_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___y_918_; lean_object* v_lib_926_; uint8_t v___x_927_; 
v_sysroot_911_ = lean_ctor_get(v_lean_910_, 0);
lean_inc_ref(v_sysroot_911_);
v_srcDir_912_ = lean_ctor_get(v_lean_910_, 2);
lean_inc_ref(v_srcDir_912_);
v_leanLibDir_913_ = lean_ctor_get(v_lean_910_, 3);
lean_inc_ref(v_leanLibDir_913_);
v_binDir_914_ = lean_ctor_get(v_lean_910_, 6);
lean_inc_ref(v_binDir_914_);
lean_dec_ref(v_lean_910_);
v___x_915_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_916_ = l_System_FilePath_join(v_srcDir_912_, v___x_915_);
v_lib_926_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__3, &l_Lake_LakeInstall_ofLean___closed__3_once, _init_l_Lake_LakeInstall_ofLean___closed__3);
v___x_927_ = l_System_Platform_isWindows;
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_inc_ref(v_leanLibDir_913_);
v___x_928_ = l_System_FilePath_join(v_leanLibDir_913_, v_lib_926_);
v___y_918_ = v___x_928_;
goto v___jp_917_;
}
else
{
lean_object* v___x_929_; 
lean_inc_ref(v_binDir_914_);
v___x_929_ = l_System_FilePath_join(v_binDir_914_, v_lib_926_);
v___y_918_ = v___x_929_;
goto v___jp_917_;
}
v___jp_917_:
{
lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_919_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_920_ = 0;
v___x_921_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_922_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_922_, 0, v___y_918_);
lean_ctor_set(v___x_922_, 1, v___x_919_);
lean_ctor_set(v___x_922_, 2, v___x_921_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*3, v___x_920_);
v___x_923_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_914_);
v___x_924_ = l_System_FilePath_join(v_binDir_914_, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_925_, 0, v_sysroot_911_);
lean_ctor_set(v___x_925_, 1, v___x_916_);
lean_ctor_set(v___x_925_, 2, v_binDir_914_);
lean_ctor_set(v___x_925_, 3, v_leanLibDir_913_);
lean_ctor_set(v___x_925_, 4, v___x_922_);
lean_ctor_set(v___x_925_, 5, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_935_ = lean_io_getenv(v___x_934_);
if (lean_obj_tag(v___x_935_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_963_; 
v_val_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_963_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_963_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_val_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_963_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___y_943_; 
v___x_940_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_941_ = lean_io_getenv(v___x_940_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_943_ = v___x_961_;
goto v___jp_942_;
}
else
{
lean_object* v_val_962_; 
v_val_962_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_val_962_);
lean_dec_ref(v___x_941_);
v___y_943_ = v_val_962_;
goto v___jp_942_;
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_startInclusive_948_; lean_object* v_endExclusive_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_string_utf8_byte_size(v___y_943_);
lean_inc_ref(v___y_943_);
v___x_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_946_, 0, v___y_943_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = l_String_Slice_trimAscii(v___x_946_);
v_startInclusive_948_ = lean_ctor_get(v___x_947_, 1);
lean_inc(v_startInclusive_948_);
v_endExclusive_949_ = lean_ctor_get(v___x_947_, 2);
lean_inc(v_endExclusive_949_);
lean_dec_ref(v___x_947_);
v___x_950_ = lean_nat_sub(v_endExclusive_949_, v_startInclusive_948_);
lean_dec(v_startInclusive_948_);
lean_dec(v_endExclusive_949_);
v___x_951_ = lean_nat_dec_eq(v___x_950_, v___x_944_);
lean_dec(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_952_ = ((lean_object*)(l_Lake_leanExe___closed__0));
lean_inc(v_val_936_);
v___x_953_ = l_System_FilePath_join(v_val_936_, v___x_952_);
v___x_954_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__2));
lean_inc(v_val_936_);
v___x_955_ = l_System_FilePath_join(v_val_936_, v___x_954_);
v___x_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_956_, 0, v_val_936_);
lean_ctor_set(v___x_956_, 1, v___y_943_);
lean_ctor_set(v___x_956_, 2, v___x_953_);
lean_ctor_set(v___x_956_, 3, v___x_955_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_956_);
v___x_958_ = v___x_938_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec_ref(v___y_943_);
lean_del_object(v___x_938_);
lean_dec(v_val_936_);
v___x_960_ = lean_box(0);
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v___x_935_);
v___x_964_ = lean_box(0);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lake_findElanInstall_x3f();
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_978_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_979_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_980_ = lean_box(0);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_983_ = 1;
v___x_984_ = 0;
v___x_985_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_985_, 0, v___x_978_);
lean_ctor_set(v___x_985_, 1, v_lean_976_);
lean_ctor_set(v___x_985_, 2, v___x_979_);
lean_ctor_set(v___x_985_, 3, v___x_980_);
lean_ctor_set(v___x_985_, 4, v___x_982_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*5, v___x_983_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*5 + 1, v___x_984_);
v___x_986_ = l_IO_Process_output(v___x_985_, v___x_980_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1005_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1005_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1005_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
uint32_t v_exitCode_991_; lean_object* v_stdout_992_; uint32_t v___x_993_; uint8_t v___x_994_; 
v_exitCode_991_ = lean_ctor_get_uint32(v_a_987_, sizeof(void*)*2);
v_stdout_992_ = lean_ctor_get(v_a_987_, 0);
lean_inc_ref(v_stdout_992_);
lean_dec(v_a_987_);
v___x_993_ = 0;
v___x_994_ = lean_uint32_dec_eq(v_exitCode_991_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v_stdout_992_);
lean_del_object(v___x_989_);
return v___x_980_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_str_998_; lean_object* v_startInclusive_999_; lean_object* v_endExclusive_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_995_ = lean_string_utf8_byte_size(v_stdout_992_);
v___x_996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_996_, 0, v_stdout_992_);
lean_ctor_set(v___x_996_, 1, v___x_981_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
v___x_997_ = l_String_Slice_trimAscii(v___x_996_);
v_str_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_str_998_);
v_startInclusive_999_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_startInclusive_999_);
v_endExclusive_1000_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_endExclusive_1000_);
lean_dec_ref(v___x_997_);
v___x_1001_ = lean_string_utf8_extract(v_str_998_, v_startInclusive_999_, v_endExclusive_1000_);
lean_dec(v_endExclusive_1000_);
lean_dec(v_startInclusive_999_);
lean_dec_ref(v_str_998_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 1);
lean_ctor_set(v___x_989_, 0, v___x_1001_);
v___x_1003_ = v___x_989_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_dec_ref(v___x_986_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lake_findLeanSysroot_x3f(v_lean_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1016_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1017_ = l_Lake_leanExe(v_sysroot_1014_);
v___x_1018_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1022_ = 1;
v___x_1023_ = 0;
v___x_1024_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1024_, 0, v___x_1016_);
lean_ctor_set(v___x_1024_, 1, v___x_1017_);
lean_ctor_set(v___x_1024_, 2, v___x_1018_);
lean_ctor_set(v___x_1024_, 3, v___x_1019_);
lean_ctor_set(v___x_1024_, 4, v___x_1021_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*5, v___x_1022_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*5 + 1, v___x_1023_);
v___x_1025_ = l_IO_Process_output(v___x_1024_, v___x_1019_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_stdout_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_str_1031_; lean_object* v_startInclusive_1032_; lean_object* v_endExclusive_1033_; lean_object* v___x_1034_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
v_stdout_1027_ = lean_ctor_get(v_a_1026_, 0);
lean_inc_ref(v_stdout_1027_);
lean_dec(v_a_1026_);
v___x_1028_ = lean_string_utf8_byte_size(v_stdout_1027_);
v___x_1029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1029_, 0, v_stdout_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1020_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
v___x_1030_ = l_String_Slice_trimAscii(v___x_1029_);
v_str_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_str_1031_);
v_startInclusive_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_startInclusive_1032_);
v_endExclusive_1033_ = lean_ctor_get(v___x_1030_, 2);
lean_inc(v_endExclusive_1033_);
lean_dec_ref(v___x_1030_);
v___x_1034_ = lean_string_utf8_extract(v_str_1031_, v_startInclusive_1032_, v_endExclusive_1033_);
lean_dec(v_endExclusive_1033_);
lean_dec(v_startInclusive_1032_);
lean_dec_ref(v_str_1031_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v___x_1025_);
v___x_1035_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1044_ = lean_io_getenv(v___x_1043_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; 
lean_dec_ref(v_sysroot_1041_);
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v___x_1044_);
return v_val_1045_;
}
else
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
lean_dec(v___x_1044_);
v___x_1046_ = l_Lake_leanArExe(v_sysroot_1041_);
v___x_1047_ = l_System_FilePath_pathExists(v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v___x_1046_);
v___x_1048_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1049_ = lean_io_getenv(v___x_1048_);
if (lean_obj_tag(v___x_1049_) == 1)
{
lean_object* v_val_1050_; 
v_val_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_val_1050_);
lean_dec_ref(v___x_1049_);
return v_val_1050_;
}
else
{
lean_object* v___x_1051_; 
lean_dec(v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
return v___x_1051_;
}
}
else
{
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1055_, lean_object* v_i_1056_, lean_object* v_cc_1057_){
_start:
{
lean_object* v_sysroot_1058_; lean_object* v_githash_1059_; lean_object* v_srcDir_1060_; lean_object* v_leanLibDir_1061_; lean_object* v_includeDir_1062_; lean_object* v_systemLibDir_1063_; lean_object* v_binDir_1064_; lean_object* v_lean_1065_; lean_object* v_leanc_1066_; lean_object* v_leantar_1067_; lean_object* v_sharedLib_1068_; lean_object* v_initSharedLib_1069_; lean_object* v_ar_1070_; lean_object* v_cFlags_1071_; lean_object* v_linkStaticFlags_1072_; lean_object* v_linkSharedFlags_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1086_; 
v_sysroot_1058_ = lean_ctor_get(v_i_1056_, 0);
v_githash_1059_ = lean_ctor_get(v_i_1056_, 1);
v_srcDir_1060_ = lean_ctor_get(v_i_1056_, 2);
v_leanLibDir_1061_ = lean_ctor_get(v_i_1056_, 3);
v_includeDir_1062_ = lean_ctor_get(v_i_1056_, 4);
v_systemLibDir_1063_ = lean_ctor_get(v_i_1056_, 5);
v_binDir_1064_ = lean_ctor_get(v_i_1056_, 6);
v_lean_1065_ = lean_ctor_get(v_i_1056_, 7);
v_leanc_1066_ = lean_ctor_get(v_i_1056_, 8);
v_leantar_1067_ = lean_ctor_get(v_i_1056_, 9);
v_sharedLib_1068_ = lean_ctor_get(v_i_1056_, 10);
v_initSharedLib_1069_ = lean_ctor_get(v_i_1056_, 11);
v_ar_1070_ = lean_ctor_get(v_i_1056_, 12);
v_cFlags_1071_ = lean_ctor_get(v_i_1056_, 14);
v_linkStaticFlags_1072_ = lean_ctor_get(v_i_1056_, 15);
v_linkSharedFlags_1073_ = lean_ctor_get(v_i_1056_, 16);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_i_1056_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1087_ = lean_ctor_get(v_i_1056_, 19);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_i_1056_, 18);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_i_1056_, 17);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_i_1056_, 13);
lean_dec(v_unused_1090_);
v___x_1075_ = v_i_1056_;
v_isShared_1076_ = v_isSharedCheck_1086_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_linkSharedFlags_1073_);
lean_inc(v_linkStaticFlags_1072_);
lean_inc(v_cFlags_1071_);
lean_inc(v_ar_1070_);
lean_inc(v_initSharedLib_1069_);
lean_inc(v_sharedLib_1068_);
lean_inc(v_leantar_1067_);
lean_inc(v_leanc_1066_);
lean_inc(v_lean_1065_);
lean_inc(v_binDir_1064_);
lean_inc(v_systemLibDir_1063_);
lean_inc(v_includeDir_1062_);
lean_inc(v_leanLibDir_1061_);
lean_inc(v_srcDir_1060_);
lean_inc(v_githash_1059_);
lean_inc(v_sysroot_1058_);
lean_dec(v_i_1056_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1086_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_ccLinkFlags_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v_ccLinkFlags_1077_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1055_);
v___x_1078_ = 0;
v___x_1079_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1055_);
lean_inc_ref(v_cFlags_1071_);
v___x_1080_ = l_Array_append___redArg(v_cFlags_1071_, v___x_1079_);
lean_dec_ref(v___x_1079_);
lean_inc_ref(v_ccLinkFlags_1077_);
v___x_1081_ = l_Array_append___redArg(v_ccLinkFlags_1077_, v_linkStaticFlags_1072_);
v___x_1082_ = l_Array_append___redArg(v_ccLinkFlags_1077_, v_linkSharedFlags_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 19, v___x_1082_);
lean_ctor_set(v___x_1075_, 18, v___x_1081_);
lean_ctor_set(v___x_1075_, 17, v___x_1080_);
lean_ctor_set(v___x_1075_, 13, v_cc_1057_);
v___x_1084_ = v___x_1075_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_sysroot_1058_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_githash_1059_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_srcDir_1060_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_leanLibDir_1061_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_includeDir_1062_);
lean_ctor_set(v_reuseFailAlloc_1085_, 5, v_systemLibDir_1063_);
lean_ctor_set(v_reuseFailAlloc_1085_, 6, v_binDir_1064_);
lean_ctor_set(v_reuseFailAlloc_1085_, 7, v_lean_1065_);
lean_ctor_set(v_reuseFailAlloc_1085_, 8, v_leanc_1066_);
lean_ctor_set(v_reuseFailAlloc_1085_, 9, v_leantar_1067_);
lean_ctor_set(v_reuseFailAlloc_1085_, 10, v_sharedLib_1068_);
lean_ctor_set(v_reuseFailAlloc_1085_, 11, v_initSharedLib_1069_);
lean_ctor_set(v_reuseFailAlloc_1085_, 12, v_ar_1070_);
lean_ctor_set(v_reuseFailAlloc_1085_, 13, v_cc_1057_);
lean_ctor_set(v_reuseFailAlloc_1085_, 14, v_cFlags_1071_);
lean_ctor_set(v_reuseFailAlloc_1085_, 15, v_linkStaticFlags_1072_);
lean_ctor_set(v_reuseFailAlloc_1085_, 16, v_linkSharedFlags_1073_);
lean_ctor_set(v_reuseFailAlloc_1085_, 17, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1085_, 18, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1085_, 19, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*20, v___x_1078_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1091_, lean_object* v_i_1092_, lean_object* v_cc_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1091_, v_i_1092_, v_cc_1093_);
lean_dec_ref(v_sysroot_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1095_, lean_object* v_cc_1096_){
_start:
{
lean_object* v_sysroot_1097_; lean_object* v_githash_1098_; lean_object* v_srcDir_1099_; lean_object* v_leanLibDir_1100_; lean_object* v_includeDir_1101_; lean_object* v_systemLibDir_1102_; lean_object* v_binDir_1103_; lean_object* v_lean_1104_; lean_object* v_leanc_1105_; lean_object* v_leantar_1106_; lean_object* v_sharedLib_1107_; lean_object* v_initSharedLib_1108_; lean_object* v_ar_1109_; uint8_t v_customCc_1110_; lean_object* v_cFlags_1111_; lean_object* v_linkStaticFlags_1112_; lean_object* v_linkSharedFlags_1113_; lean_object* v_ccFlags_1114_; lean_object* v_ccLinkStaticFlags_1115_; lean_object* v_ccLinkSharedFlags_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_sysroot_1097_ = lean_ctor_get(v_i_1095_, 0);
v_githash_1098_ = lean_ctor_get(v_i_1095_, 1);
v_srcDir_1099_ = lean_ctor_get(v_i_1095_, 2);
v_leanLibDir_1100_ = lean_ctor_get(v_i_1095_, 3);
v_includeDir_1101_ = lean_ctor_get(v_i_1095_, 4);
v_systemLibDir_1102_ = lean_ctor_get(v_i_1095_, 5);
v_binDir_1103_ = lean_ctor_get(v_i_1095_, 6);
v_lean_1104_ = lean_ctor_get(v_i_1095_, 7);
v_leanc_1105_ = lean_ctor_get(v_i_1095_, 8);
v_leantar_1106_ = lean_ctor_get(v_i_1095_, 9);
v_sharedLib_1107_ = lean_ctor_get(v_i_1095_, 10);
v_initSharedLib_1108_ = lean_ctor_get(v_i_1095_, 11);
v_ar_1109_ = lean_ctor_get(v_i_1095_, 12);
v_customCc_1110_ = lean_ctor_get_uint8(v_i_1095_, sizeof(void*)*20);
v_cFlags_1111_ = lean_ctor_get(v_i_1095_, 14);
v_linkStaticFlags_1112_ = lean_ctor_get(v_i_1095_, 15);
v_linkSharedFlags_1113_ = lean_ctor_get(v_i_1095_, 16);
v_ccFlags_1114_ = lean_ctor_get(v_i_1095_, 17);
v_ccLinkStaticFlags_1115_ = lean_ctor_get(v_i_1095_, 18);
v_ccLinkSharedFlags_1116_ = lean_ctor_get(v_i_1095_, 19);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_i_1095_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_i_1095_, 13);
lean_dec(v_unused_1124_);
v___x_1118_ = v_i_1095_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1116_);
lean_inc(v_ccLinkStaticFlags_1115_);
lean_inc(v_ccFlags_1114_);
lean_inc(v_linkSharedFlags_1113_);
lean_inc(v_linkStaticFlags_1112_);
lean_inc(v_cFlags_1111_);
lean_inc(v_ar_1109_);
lean_inc(v_initSharedLib_1108_);
lean_inc(v_sharedLib_1107_);
lean_inc(v_leantar_1106_);
lean_inc(v_leanc_1105_);
lean_inc(v_lean_1104_);
lean_inc(v_binDir_1103_);
lean_inc(v_systemLibDir_1102_);
lean_inc(v_includeDir_1101_);
lean_inc(v_leanLibDir_1100_);
lean_inc(v_srcDir_1099_);
lean_inc(v_githash_1098_);
lean_inc(v_sysroot_1097_);
lean_dec(v_i_1095_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 13, v_cc_1096_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_sysroot_1097_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_githash_1098_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_srcDir_1099_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_leanLibDir_1100_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_includeDir_1101_);
lean_ctor_set(v_reuseFailAlloc_1122_, 5, v_systemLibDir_1102_);
lean_ctor_set(v_reuseFailAlloc_1122_, 6, v_binDir_1103_);
lean_ctor_set(v_reuseFailAlloc_1122_, 7, v_lean_1104_);
lean_ctor_set(v_reuseFailAlloc_1122_, 8, v_leanc_1105_);
lean_ctor_set(v_reuseFailAlloc_1122_, 9, v_leantar_1106_);
lean_ctor_set(v_reuseFailAlloc_1122_, 10, v_sharedLib_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 11, v_initSharedLib_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 12, v_ar_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 13, v_cc_1096_);
lean_ctor_set(v_reuseFailAlloc_1122_, 14, v_cFlags_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 15, v_linkStaticFlags_1112_);
lean_ctor_set(v_reuseFailAlloc_1122_, 16, v_linkSharedFlags_1113_);
lean_ctor_set(v_reuseFailAlloc_1122_, 17, v_ccFlags_1114_);
lean_ctor_set(v_reuseFailAlloc_1122_, 18, v_ccLinkStaticFlags_1115_);
lean_ctor_set(v_reuseFailAlloc_1122_, 19, v_ccLinkSharedFlags_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*20, v_customCc_1110_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1127_, lean_object* v_i_1128_){
_start:
{
lean_object* v_cc_1131_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1161_ = lean_io_getenv(v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; 
lean_dec_ref(v_sysroot_1127_);
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v___x_1161_);
v_cc_1131_ = v_val_1162_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
lean_dec(v___x_1161_);
lean_inc_ref(v_sysroot_1127_);
v___x_1163_ = l_Lake_leanCcExe(v_sysroot_1127_);
v___x_1164_ = l_System_FilePath_pathExists(v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v___x_1163_);
lean_dec_ref(v_sysroot_1127_);
v___x_1165_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1166_ = lean_io_getenv(v___x_1165_);
if (lean_obj_tag(v___x_1166_) == 1)
{
lean_object* v_val_1167_; 
v_val_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_val_1167_);
lean_dec_ref(v___x_1166_);
v_cc_1131_ = v_val_1167_;
goto v___jp_1130_;
}
else
{
lean_object* v_sysroot_1168_; lean_object* v_githash_1169_; lean_object* v_srcDir_1170_; lean_object* v_leanLibDir_1171_; lean_object* v_includeDir_1172_; lean_object* v_systemLibDir_1173_; lean_object* v_binDir_1174_; lean_object* v_lean_1175_; lean_object* v_leanc_1176_; lean_object* v_leantar_1177_; lean_object* v_sharedLib_1178_; lean_object* v_initSharedLib_1179_; lean_object* v_ar_1180_; uint8_t v_customCc_1181_; lean_object* v_cFlags_1182_; lean_object* v_linkStaticFlags_1183_; lean_object* v_linkSharedFlags_1184_; lean_object* v_ccFlags_1185_; lean_object* v_ccLinkStaticFlags_1186_; lean_object* v_ccLinkSharedFlags_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v___x_1166_);
v_sysroot_1168_ = lean_ctor_get(v_i_1128_, 0);
v_githash_1169_ = lean_ctor_get(v_i_1128_, 1);
v_srcDir_1170_ = lean_ctor_get(v_i_1128_, 2);
v_leanLibDir_1171_ = lean_ctor_get(v_i_1128_, 3);
v_includeDir_1172_ = lean_ctor_get(v_i_1128_, 4);
v_systemLibDir_1173_ = lean_ctor_get(v_i_1128_, 5);
v_binDir_1174_ = lean_ctor_get(v_i_1128_, 6);
v_lean_1175_ = lean_ctor_get(v_i_1128_, 7);
v_leanc_1176_ = lean_ctor_get(v_i_1128_, 8);
v_leantar_1177_ = lean_ctor_get(v_i_1128_, 9);
v_sharedLib_1178_ = lean_ctor_get(v_i_1128_, 10);
v_initSharedLib_1179_ = lean_ctor_get(v_i_1128_, 11);
v_ar_1180_ = lean_ctor_get(v_i_1128_, 12);
v_customCc_1181_ = lean_ctor_get_uint8(v_i_1128_, sizeof(void*)*20);
v_cFlags_1182_ = lean_ctor_get(v_i_1128_, 14);
v_linkStaticFlags_1183_ = lean_ctor_get(v_i_1128_, 15);
v_linkSharedFlags_1184_ = lean_ctor_get(v_i_1128_, 16);
v_ccFlags_1185_ = lean_ctor_get(v_i_1128_, 17);
v_ccLinkStaticFlags_1186_ = lean_ctor_get(v_i_1128_, 18);
v_ccLinkSharedFlags_1187_ = lean_ctor_get(v_i_1128_, 19);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_i_1128_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_i_1128_, 13);
lean_dec(v_unused_1196_);
v___x_1189_ = v_i_1128_;
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1187_);
lean_inc(v_ccLinkStaticFlags_1186_);
lean_inc(v_ccFlags_1185_);
lean_inc(v_linkSharedFlags_1184_);
lean_inc(v_linkStaticFlags_1183_);
lean_inc(v_cFlags_1182_);
lean_inc(v_ar_1180_);
lean_inc(v_initSharedLib_1179_);
lean_inc(v_sharedLib_1178_);
lean_inc(v_leantar_1177_);
lean_inc(v_leanc_1176_);
lean_inc(v_lean_1175_);
lean_inc(v_binDir_1174_);
lean_inc(v_systemLibDir_1173_);
lean_inc(v_includeDir_1172_);
lean_inc(v_leanLibDir_1171_);
lean_inc(v_srcDir_1170_);
lean_inc(v_githash_1169_);
lean_inc(v_sysroot_1168_);
lean_dec(v_i_1128_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__29));
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 13, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_sysroot_1168_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_githash_1169_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_srcDir_1170_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_leanLibDir_1171_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_includeDir_1172_);
lean_ctor_set(v_reuseFailAlloc_1194_, 5, v_systemLibDir_1173_);
lean_ctor_set(v_reuseFailAlloc_1194_, 6, v_binDir_1174_);
lean_ctor_set(v_reuseFailAlloc_1194_, 7, v_lean_1175_);
lean_ctor_set(v_reuseFailAlloc_1194_, 8, v_leanc_1176_);
lean_ctor_set(v_reuseFailAlloc_1194_, 9, v_leantar_1177_);
lean_ctor_set(v_reuseFailAlloc_1194_, 10, v_sharedLib_1178_);
lean_ctor_set(v_reuseFailAlloc_1194_, 11, v_initSharedLib_1179_);
lean_ctor_set(v_reuseFailAlloc_1194_, 12, v_ar_1180_);
lean_ctor_set(v_reuseFailAlloc_1194_, 13, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1194_, 14, v_cFlags_1182_);
lean_ctor_set(v_reuseFailAlloc_1194_, 15, v_linkStaticFlags_1183_);
lean_ctor_set(v_reuseFailAlloc_1194_, 16, v_linkSharedFlags_1184_);
lean_ctor_set(v_reuseFailAlloc_1194_, 17, v_ccFlags_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 18, v_ccLinkStaticFlags_1186_);
lean_ctor_set(v_reuseFailAlloc_1194_, 19, v_ccLinkSharedFlags_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1194_, sizeof(void*)*20, v_customCc_1181_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1127_, v_i_1128_, v___x_1163_);
lean_dec_ref(v_sysroot_1127_);
return v___x_1197_;
}
}
v___jp_1130_:
{
lean_object* v_sysroot_1132_; lean_object* v_githash_1133_; lean_object* v_srcDir_1134_; lean_object* v_leanLibDir_1135_; lean_object* v_includeDir_1136_; lean_object* v_systemLibDir_1137_; lean_object* v_binDir_1138_; lean_object* v_lean_1139_; lean_object* v_leanc_1140_; lean_object* v_leantar_1141_; lean_object* v_sharedLib_1142_; lean_object* v_initSharedLib_1143_; lean_object* v_ar_1144_; uint8_t v_customCc_1145_; lean_object* v_cFlags_1146_; lean_object* v_linkStaticFlags_1147_; lean_object* v_linkSharedFlags_1148_; lean_object* v_ccFlags_1149_; lean_object* v_ccLinkStaticFlags_1150_; lean_object* v_ccLinkSharedFlags_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_sysroot_1132_ = lean_ctor_get(v_i_1128_, 0);
v_githash_1133_ = lean_ctor_get(v_i_1128_, 1);
v_srcDir_1134_ = lean_ctor_get(v_i_1128_, 2);
v_leanLibDir_1135_ = lean_ctor_get(v_i_1128_, 3);
v_includeDir_1136_ = lean_ctor_get(v_i_1128_, 4);
v_systemLibDir_1137_ = lean_ctor_get(v_i_1128_, 5);
v_binDir_1138_ = lean_ctor_get(v_i_1128_, 6);
v_lean_1139_ = lean_ctor_get(v_i_1128_, 7);
v_leanc_1140_ = lean_ctor_get(v_i_1128_, 8);
v_leantar_1141_ = lean_ctor_get(v_i_1128_, 9);
v_sharedLib_1142_ = lean_ctor_get(v_i_1128_, 10);
v_initSharedLib_1143_ = lean_ctor_get(v_i_1128_, 11);
v_ar_1144_ = lean_ctor_get(v_i_1128_, 12);
v_customCc_1145_ = lean_ctor_get_uint8(v_i_1128_, sizeof(void*)*20);
v_cFlags_1146_ = lean_ctor_get(v_i_1128_, 14);
v_linkStaticFlags_1147_ = lean_ctor_get(v_i_1128_, 15);
v_linkSharedFlags_1148_ = lean_ctor_get(v_i_1128_, 16);
v_ccFlags_1149_ = lean_ctor_get(v_i_1128_, 17);
v_ccLinkStaticFlags_1150_ = lean_ctor_get(v_i_1128_, 18);
v_ccLinkSharedFlags_1151_ = lean_ctor_get(v_i_1128_, 19);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_i_1128_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_i_1128_, 13);
lean_dec(v_unused_1159_);
v___x_1153_ = v_i_1128_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1151_);
lean_inc(v_ccLinkStaticFlags_1150_);
lean_inc(v_ccFlags_1149_);
lean_inc(v_linkSharedFlags_1148_);
lean_inc(v_linkStaticFlags_1147_);
lean_inc(v_cFlags_1146_);
lean_inc(v_ar_1144_);
lean_inc(v_initSharedLib_1143_);
lean_inc(v_sharedLib_1142_);
lean_inc(v_leantar_1141_);
lean_inc(v_leanc_1140_);
lean_inc(v_lean_1139_);
lean_inc(v_binDir_1138_);
lean_inc(v_systemLibDir_1137_);
lean_inc(v_includeDir_1136_);
lean_inc(v_leanLibDir_1135_);
lean_inc(v_srcDir_1134_);
lean_inc(v_githash_1133_);
lean_inc(v_sysroot_1132_);
lean_dec(v_i_1128_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 13, v_cc_1131_);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_sysroot_1132_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_githash_1133_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_srcDir_1134_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_leanLibDir_1135_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_includeDir_1136_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_systemLibDir_1137_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_binDir_1138_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v_lean_1139_);
lean_ctor_set(v_reuseFailAlloc_1157_, 8, v_leanc_1140_);
lean_ctor_set(v_reuseFailAlloc_1157_, 9, v_leantar_1141_);
lean_ctor_set(v_reuseFailAlloc_1157_, 10, v_sharedLib_1142_);
lean_ctor_set(v_reuseFailAlloc_1157_, 11, v_initSharedLib_1143_);
lean_ctor_set(v_reuseFailAlloc_1157_, 12, v_ar_1144_);
lean_ctor_set(v_reuseFailAlloc_1157_, 13, v_cc_1131_);
lean_ctor_set(v_reuseFailAlloc_1157_, 14, v_cFlags_1146_);
lean_ctor_set(v_reuseFailAlloc_1157_, 15, v_linkStaticFlags_1147_);
lean_ctor_set(v_reuseFailAlloc_1157_, 16, v_linkSharedFlags_1148_);
lean_ctor_set(v_reuseFailAlloc_1157_, 17, v_ccFlags_1149_);
lean_ctor_set(v_reuseFailAlloc_1157_, 18, v_ccLinkStaticFlags_1150_);
lean_ctor_set(v_reuseFailAlloc_1157_, 19, v_ccLinkSharedFlags_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*20, v_customCc_1145_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1198_, lean_object* v_i_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1198_, v_i_1199_);
return v_res_1201_;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__3(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__2));
v___x_1206_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_1207_ = lean_array_push(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__4(void){
_start:
{
uint8_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = 1;
v___x_1209_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__5(void){
_start:
{
uint8_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = 0;
v___x_1211_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1212_, uint8_t v_collocated_1213_){
_start:
{
lean_object* v_githash_1216_; 
if (v_collocated_1213_ == 0)
{
lean_object* v___x_1244_; 
lean_inc_ref(v_sysroot_1212_);
v___x_1244_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1212_);
v_githash_1216_ = v___x_1244_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_githash;
v_githash_1216_ = v___x_1245_;
goto v___jp_1215_;
}
v___jp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_inc_ref(v_sysroot_1212_);
v___x_1217_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1212_);
v___x_1218_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__0));
lean_inc_ref(v_sysroot_1212_);
v___x_1219_ = l_System_FilePath_join(v_sysroot_1212_, v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1221_ = l_System_FilePath_join(v___x_1219_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
lean_inc_ref(v_sysroot_1212_);
v___x_1223_ = l_System_FilePath_join(v_sysroot_1212_, v___x_1222_);
lean_inc_ref(v___x_1223_);
v___x_1224_ = l_System_FilePath_join(v___x_1223_, v___x_1220_);
v___x_1225_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__1));
lean_inc_ref(v_sysroot_1212_);
v___x_1226_ = l_System_FilePath_join(v_sysroot_1212_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_Lake_leanExe___closed__0));
lean_inc_ref(v_sysroot_1212_);
v___x_1228_ = l_System_FilePath_join(v_sysroot_1212_, v___x_1227_);
lean_inc_ref(v_sysroot_1212_);
v___x_1229_ = l_Lake_leanExe(v_sysroot_1212_);
lean_inc_ref(v_sysroot_1212_);
v___x_1230_ = l_Lake_leancExe(v_sysroot_1212_);
lean_inc_ref(v_sysroot_1212_);
v___x_1231_ = l_Lake_leantarExe(v_sysroot_1212_);
lean_inc_ref(v_sysroot_1212_);
v___x_1232_ = l_Lake_leanSharedLibDir(v_sysroot_1212_);
v___x_1233_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1232_);
v___x_1234_ = l_System_FilePath_join(v___x_1232_, v___x_1233_);
v___x_1235_ = l_Lake_initSharedLib;
v___x_1236_ = l_System_FilePath_join(v___x_1232_, v___x_1235_);
v___x_1237_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__29));
v___x_1238_ = 1;
v___x_1239_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__3, &l_Lake_LeanInstall_get___closed__3_once, _init_l_Lake_LeanInstall_get___closed__3);
v___x_1240_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__4, &l_Lake_LeanInstall_get___closed__4_once, _init_l_Lake_LeanInstall_get___closed__4);
v___x_1241_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__5, &l_Lake_LeanInstall_get___closed__5_once, _init_l_Lake_LeanInstall_get___closed__5);
lean_inc_ref(v_sysroot_1212_);
v___x_1242_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v___x_1242_, 0, v_sysroot_1212_);
lean_ctor_set(v___x_1242_, 1, v_githash_1216_);
lean_ctor_set(v___x_1242_, 2, v___x_1221_);
lean_ctor_set(v___x_1242_, 3, v___x_1224_);
lean_ctor_set(v___x_1242_, 4, v___x_1226_);
lean_ctor_set(v___x_1242_, 5, v___x_1223_);
lean_ctor_set(v___x_1242_, 6, v___x_1228_);
lean_ctor_set(v___x_1242_, 7, v___x_1229_);
lean_ctor_set(v___x_1242_, 8, v___x_1230_);
lean_ctor_set(v___x_1242_, 9, v___x_1231_);
lean_ctor_set(v___x_1242_, 10, v___x_1234_);
lean_ctor_set(v___x_1242_, 11, v___x_1236_);
lean_ctor_set(v___x_1242_, 12, v___x_1217_);
lean_ctor_set(v___x_1242_, 13, v___x_1237_);
lean_ctor_set(v___x_1242_, 14, v___x_1239_);
lean_ctor_set(v___x_1242_, 15, v___x_1240_);
lean_ctor_set(v___x_1242_, 16, v___x_1241_);
lean_ctor_set(v___x_1242_, 17, v___x_1239_);
lean_ctor_set(v___x_1242_, 18, v___x_1240_);
lean_ctor_set(v___x_1242_, 19, v___x_1241_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*20, v___x_1238_);
v___x_1243_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1212_, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1246_, lean_object* v_collocated_1247_, lean_object* v_a_1248_){
_start:
{
uint8_t v_collocated_boxed_1249_; lean_object* v_res_1250_; 
v_collocated_boxed_1249_ = lean_unbox(v_collocated_1247_);
v_res_1250_ = l_Lake_LeanInstall_get(v_sysroot_1246_, v_collocated_boxed_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lake_findLeanSysroot_x3f(v_lean_1251_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_val_1255_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v___x_1253_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v___x_1253_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1259_ = 0;
v___x_1260_ = l_Lake_LeanInstall_get(v_val_1255_, v___x_1259_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_io_app_path();
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_System_FilePath_parent(v_a_1272_);
if (lean_obj_tag(v___x_1273_) == 1)
{
lean_object* v_val_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_val_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref(v___x_1273_);
v___x_1275_ = ((lean_object*)(l_Lake_leanExe___closed__1));
lean_inc(v_val_1274_);
v___x_1276_ = l_System_FilePath_join(v_val_1274_, v___x_1275_);
v___x_1277_ = l_System_FilePath_exeExtension;
v___x_1278_ = l_System_FilePath_addExtension(v___x_1276_, v___x_1277_);
v___x_1279_ = l_System_FilePath_pathExists(v___x_1278_);
lean_dec_ref(v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec(v_val_1274_);
goto v___jp_1269_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = l_System_FilePath_parent(v_val_1274_);
return v___x_1280_;
}
}
else
{
lean_dec(v___x_1273_);
goto v___jp_1269_;
}
}
else
{
lean_dec_ref(v___x_1271_);
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_box(0);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_System_FilePath_parent(v_lake_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = l_System_FilePath_parent(v_val_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
return v___x_1286_;
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1288_; 
v_val_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_val_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = l_System_FilePath_parent(v_val_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
return v___x_1288_;
}
else
{
lean_object* v_val_1289_; lean_object* v___x_1290_; 
v_val_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1289_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = l_System_FilePath_parent(v_val_1289_);
return v___x_1290_;
}
}
}
}
}
static lean_object* _init_l_Lake_getLakeInstall_x3f___closed__1(void){
_start:
{
uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = 0;
v___x_1293_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1294_ = l_Lake_nameToSharedLib(v___x_1293_, v___x_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1296_){
_start:
{
lean_object* v___x_1298_; 
lean_inc_ref(v_lake_1296_);
v___x_1298_ = l_Lake_lakeBuildHome_x3f(v_lake_1296_);
if (lean_obj_tag(v___x_1298_) == 1)
{
lean_object* v_val_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1323_; 
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_val_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_lake_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1303_ = l_Lake_defaultBuildDir;
lean_inc(v_val_1299_);
v___x_1304_ = l_System_FilePath_join(v_val_1299_, v___x_1303_);
v___x_1305_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1304_);
v___x_1306_ = l_System_FilePath_join(v___x_1304_, v___x_1305_);
v___x_1307_ = l_Lake_defaultLeanLibDir;
v___x_1308_ = l_System_FilePath_join(v___x_1304_, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1310_ = 0;
v___x_1311_ = lean_obj_once(&l_Lake_getLakeInstall_x3f___closed__1, &l_Lake_getLakeInstall_x3f___closed__1_once, _init_l_Lake_getLakeInstall_x3f___closed__1);
lean_inc_ref(v___x_1308_);
v___x_1312_ = l_System_FilePath_join(v___x_1308_, v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1314_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1309_);
lean_ctor_set(v___x_1314_, 2, v___x_1313_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*3, v___x_1310_);
lean_inc_ref(v___x_1308_);
lean_inc(v_val_1299_);
v_lake_1315_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1315_, 0, v_val_1299_);
lean_ctor_set(v_lake_1315_, 1, v_val_1299_);
lean_ctor_set(v_lake_1315_, 2, v___x_1306_);
lean_ctor_set(v_lake_1315_, 3, v___x_1308_);
lean_ctor_set(v_lake_1315_, 4, v___x_1314_);
lean_ctor_set(v_lake_1315_, 5, v_lake_1296_);
v___x_1316_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__2));
v___x_1317_ = l_System_FilePath_join(v___x_1308_, v___x_1316_);
v___x_1318_ = l_System_FilePath_pathExists(v___x_1317_);
lean_dec_ref(v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref(v_lake_1315_);
lean_del_object(v___x_1301_);
v___x_1319_ = lean_box(0);
return v___x_1319_;
}
else
{
lean_object* v___x_1321_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v_lake_1315_);
v___x_1321_ = v___x_1301_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_lake_1315_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v___x_1324_; 
lean_dec(v___x_1298_);
lean_dec_ref(v_lake_1296_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_getLakeInstall_x3f(v_lake_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1332_ = lean_io_getenv(v___x_1331_);
if (lean_obj_tag(v___x_1332_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
v_val_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_val_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = 0;
v___x_1338_ = l_Lake_LeanInstall_get(v_val_1333_, v___x_1337_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_lean_1346_; 
lean_dec(v___x_1332_);
v___x_1343_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1344_ = lean_io_getenv(v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_startInclusive_1364_; lean_object* v_endExclusive_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_val_1359_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1359_);
lean_dec_ref(v___x_1344_);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_string_utf8_byte_size(v_val_1359_);
lean_inc(v_val_1359_);
v___x_1362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1362_, 0, v_val_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1360_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = l_String_Slice_trimAscii(v___x_1362_);
v_startInclusive_1364_ = lean_ctor_get(v___x_1363_, 1);
lean_inc(v_startInclusive_1364_);
v_endExclusive_1365_ = lean_ctor_get(v___x_1363_, 2);
lean_inc(v_endExclusive_1365_);
lean_dec_ref(v___x_1363_);
v___x_1366_ = lean_nat_sub(v_endExclusive_1365_, v_startInclusive_1364_);
lean_dec(v_startInclusive_1364_);
lean_dec(v_endExclusive_1365_);
v___x_1367_ = lean_nat_dec_eq(v___x_1366_, v___x_1360_);
lean_dec(v___x_1366_);
if (v___x_1367_ == 0)
{
v_lean_1346_ = v_val_1359_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1368_; 
lean_dec(v_val_1359_);
v___x_1368_ = lean_box(0);
return v___x_1368_;
}
}
else
{
lean_object* v___x_1369_; 
lean_dec(v___x_1344_);
v___x_1369_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v_lean_1346_ = v___x_1369_;
goto v___jp_1345_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lake_findLeanSysroot_x3f(v_lean_1346_);
if (lean_obj_tag(v___x_1347_) == 1)
{
lean_object* v_val_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1357_; 
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_val_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = 0;
v___x_1353_ = l_Lake_LeanInstall_get(v_val_1348_, v___x_1352_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1353_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v___x_1358_; 
lean_dec(v___x_1347_);
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lake_findLeanInstall_x3f();
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_io_app_path();
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = l_Lake_getLakeInstall_x3f(v_a_1402_);
if (lean_obj_tag(v___x_1403_) == 1)
{
return v___x_1403_;
}
else
{
lean_dec(v___x_1403_);
goto v___jp_1374_;
}
}
else
{
lean_dec_ref(v___x_1401_);
goto v___jp_1374_;
}
v___jp_1374_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1376_ = lean_io_getenv(v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1399_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1399_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1399_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1381_ = l_Lake_defaultBuildDir;
lean_inc(v_val_1377_);
v___x_1382_ = l_System_FilePath_join(v_val_1377_, v___x_1381_);
v___x_1383_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1382_);
v___x_1384_ = l_System_FilePath_join(v___x_1382_, v___x_1383_);
v___x_1385_ = l_Lake_defaultLeanLibDir;
v___x_1386_ = l_System_FilePath_join(v___x_1382_, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1388_ = 0;
v___x_1389_ = lean_obj_once(&l_Lake_getLakeInstall_x3f___closed__1, &l_Lake_getLakeInstall_x3f___closed__1_once, _init_l_Lake_getLakeInstall_x3f___closed__1);
lean_inc_ref(v___x_1386_);
v___x_1390_ = l_System_FilePath_join(v___x_1386_, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1392_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1387_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*3, v___x_1388_);
v___x_1393_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1384_);
v___x_1394_ = l_System_FilePath_join(v___x_1384_, v___x_1393_);
lean_inc(v_val_1377_);
v___x_1395_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1395_, 0, v_val_1377_);
lean_ctor_set(v___x_1395_, 1, v_val_1377_);
lean_ctor_set(v___x_1395_, 2, v___x_1384_);
lean_ctor_set(v___x_1395_, 3, v___x_1386_);
lean_ctor_set(v___x_1395_, 4, v___x_1392_);
lean_ctor_set(v___x_1395_, 5, v___x_1394_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1395_);
v___x_1397_ = v___x_1379_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v___x_1400_; 
lean_dec(v___x_1376_);
v___x_1400_ = lean_box(0);
return v___x_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lake_findLakeInstall_x3f();
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = l_Lake_findElanInstall_x3f();
v___x_1409_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1409_) == 1)
{
lean_object* v_val_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1469_; 
v_val_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1469_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_val_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1469_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1415_ = lean_io_getenv(v___x_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
goto v___jp_1416_;
}
else
{
lean_object* v_val_1426_; lean_object* v___x_1427_; 
v_val_1426_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___x_1415_);
v___x_1427_ = l_Lake_envToBool_x3f(v_val_1426_);
if (lean_obj_tag(v___x_1427_) == 0)
{
goto v___jp_1416_;
}
else
{
lean_object* v_val_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1468_; 
v_val_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1468_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_val_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1468_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_unbox(v_val_1428_);
if (v___x_1432_ == 0)
{
lean_del_object(v___x_1430_);
lean_dec(v_val_1428_);
goto v___jp_1416_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_del_object(v___x_1412_);
v___x_1433_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
v___x_1434_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__0));
lean_inc(v_val_1410_);
v___x_1435_ = l_System_FilePath_join(v_val_1410_, v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1437_ = l_System_FilePath_join(v___x_1435_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
lean_inc(v_val_1410_);
v___x_1439_ = l_System_FilePath_join(v_val_1410_, v___x_1438_);
lean_inc_ref(v___x_1439_);
v___x_1440_ = l_System_FilePath_join(v___x_1439_, v___x_1436_);
v___x_1441_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__1));
lean_inc(v_val_1410_);
v___x_1442_ = l_System_FilePath_join(v_val_1410_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Lake_leanExe___closed__0));
lean_inc(v_val_1410_);
v___x_1444_ = l_System_FilePath_join(v_val_1410_, v___x_1443_);
lean_inc(v_val_1410_);
v___x_1445_ = l_Lake_leanExe(v_val_1410_);
lean_inc(v_val_1410_);
v___x_1446_ = l_Lake_leancExe(v_val_1410_);
lean_inc(v_val_1410_);
v___x_1447_ = l_Lake_leantarExe(v_val_1410_);
lean_inc(v_val_1410_);
v___x_1448_ = l_Lake_leanSharedLibDir(v_val_1410_);
v___x_1449_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1448_);
v___x_1450_ = l_System_FilePath_join(v___x_1448_, v___x_1449_);
v___x_1451_ = l_Lake_initSharedLib;
v___x_1452_ = l_System_FilePath_join(v___x_1448_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_1454_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__29));
v___x_1455_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__3, &l_Lake_LeanInstall_get___closed__3_once, _init_l_Lake_LeanInstall_get___closed__3);
v___x_1456_ = lean_unbox(v_val_1428_);
v___x_1457_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1456_);
v___x_1458_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__5, &l_Lake_LeanInstall_get___closed__5_once, _init_l_Lake_LeanInstall_get___closed__5);
lean_inc_ref(v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 20, 1);
lean_ctor_set(v___x_1459_, 0, v_val_1410_);
lean_ctor_set(v___x_1459_, 1, v___x_1433_);
lean_ctor_set(v___x_1459_, 2, v___x_1437_);
lean_ctor_set(v___x_1459_, 3, v___x_1440_);
lean_ctor_set(v___x_1459_, 4, v___x_1442_);
lean_ctor_set(v___x_1459_, 5, v___x_1439_);
lean_ctor_set(v___x_1459_, 6, v___x_1444_);
lean_ctor_set(v___x_1459_, 7, v___x_1445_);
lean_ctor_set(v___x_1459_, 8, v___x_1446_);
lean_ctor_set(v___x_1459_, 9, v___x_1447_);
lean_ctor_set(v___x_1459_, 10, v___x_1450_);
lean_ctor_set(v___x_1459_, 11, v___x_1452_);
lean_ctor_set(v___x_1459_, 12, v___x_1453_);
lean_ctor_set(v___x_1459_, 13, v___x_1454_);
lean_ctor_set(v___x_1459_, 14, v___x_1455_);
lean_ctor_set(v___x_1459_, 15, v___x_1457_);
lean_ctor_set(v___x_1459_, 16, v___x_1458_);
lean_ctor_set(v___x_1459_, 17, v___x_1455_);
lean_ctor_set(v___x_1459_, 18, v___x_1457_);
lean_ctor_set(v___x_1459_, 19, v___x_1458_);
v___x_1460_ = lean_unbox(v_val_1428_);
lean_dec(v_val_1428_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*20, v___x_1460_);
v___x_1461_ = l_Lake_findLeanInstall_x3f();
v___x_1462_ = l_Lake_LakeInstall_ofLean(v___x_1459_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1462_);
v___x_1464_ = v___x_1430_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1461_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1408_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
return v___x_1466_;
}
}
}
}
}
v___jp_1416_:
{
uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1417_ = 1;
v___x_1418_ = l_Lake_LeanInstall_get(v_val_1410_, v___x_1417_);
lean_inc_ref(v___x_1418_);
v___x_1419_ = l_Lake_LakeInstall_ofLean(v___x_1418_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1418_);
v___x_1421_ = v___x_1412_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1418_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1419_);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1408_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
return v___x_1424_;
}
}
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1409_);
v___x_1470_ = l_Lake_findLeanInstall_x3f();
v___x_1471_ = l_Lake_findLakeInstall_x3f();
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1408_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lake_findInstall_x3f();
return v_res_1475_;
}
}
lean_object* runtime_initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
