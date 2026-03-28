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
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
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
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leanirExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leancExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__19 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__20;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_leantarExe___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__21 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__21_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sharedLib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__22 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__23 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__23_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__24;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "initSharedLib"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__25 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__25_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__26 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__26_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ar"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__27 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__27_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__27_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__28 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__28_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__29;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "cc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__30 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__31 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__31_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "customCc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__32 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__32_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__32_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__33 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__33_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__34;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__35 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__36 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__36_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__37 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__37_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__37_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__38 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__38_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__39;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ccFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__43 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__43_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__44 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__44_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__44_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__45_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__46;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__47 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__47_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__47_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__48 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__48_value;
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
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object* v_sysroot_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_264_ = l_System_FilePath_join(v_sysroot_262_, v___x_263_);
v___x_265_ = ((lean_object*)(l_Lake_leanirExe___closed__0));
v___x_266_ = l_System_FilePath_join(v___x_264_, v___x_265_);
v___x_267_ = l_System_FilePath_exeExtension;
v___x_268_ = l_System_FilePath_addExtension(v___x_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_271_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_272_ = l_System_FilePath_join(v_sysroot_270_, v___x_271_);
v___x_273_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_274_ = l_System_FilePath_join(v___x_272_, v___x_273_);
v___x_275_ = l_System_FilePath_exeExtension;
v___x_276_ = l_System_FilePath_addExtension(v___x_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_280_ = l_System_FilePath_join(v_sysroot_278_, v___x_279_);
v___x_281_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_282_ = l_System_FilePath_join(v___x_280_, v___x_281_);
v___x_283_ = l_System_FilePath_exeExtension;
v___x_284_ = l_System_FilePath_addExtension(v___x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_288_ = l_System_FilePath_join(v_sysroot_286_, v___x_287_);
v___x_289_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_290_ = l_System_FilePath_join(v___x_288_, v___x_289_);
v___x_291_ = l_System_FilePath_exeExtension;
v___x_292_ = l_System_FilePath_addExtension(v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_296_ = l_System_FilePath_join(v_sysroot_294_, v___x_295_);
v___x_297_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_298_ = l_System_FilePath_join(v___x_296_, v___x_297_);
v___x_299_ = l_System_FilePath_exeExtension;
v___x_300_ = l_System_FilePath_addExtension(v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_System_Platform_isWindows;
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_305_ = l_System_FilePath_join(v_sysroot_302_, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_307_ = l_System_FilePath_join(v___x_305_, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_309_ = l_System_FilePath_join(v_sysroot_302_, v___x_308_);
return v___x_309_;
}
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l_Lake_sharedLibExt;
v___x_312_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_313_ = l_System_FilePath_addExtension(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_314_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = l_Lake_sharedLibExt;
v___x_317_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_318_ = l_System_FilePath_addExtension(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_322_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_323_ = 0;
v___x_324_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
v___x_325_ = l_System_instInhabitedFilePath_default;
v___x_326_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
lean_ctor_set(v___x_326_, 4, v___x_325_);
lean_ctor_set(v___x_326_, 5, v___x_325_);
lean_ctor_set(v___x_326_, 6, v___x_325_);
lean_ctor_set(v___x_326_, 7, v___x_325_);
lean_ctor_set(v___x_326_, 8, v___x_325_);
lean_ctor_set(v___x_326_, 9, v___x_325_);
lean_ctor_set(v___x_326_, 10, v___x_325_);
lean_ctor_set(v___x_326_, 11, v___x_325_);
lean_ctor_set(v___x_326_, 12, v___x_325_);
lean_ctor_set(v___x_326_, 13, v___x_325_);
lean_ctor_set(v___x_326_, 14, v___x_325_);
lean_ctor_set(v___x_326_, 15, v___x_322_);
lean_ctor_set(v___x_326_, 16, v___x_322_);
lean_ctor_set(v___x_326_, 17, v___x_322_);
lean_ctor_set(v___x_326_, 18, v___x_322_);
lean_ctor_set(v___x_326_, 19, v___x_322_);
lean_ctor_set(v___x_326_, 20, v___x_322_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*21, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
return v___x_327_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object* v___y_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = l_String_quote(v___y_329_);
v___x_331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_dec(v_x_332_);
return v_x_333_;
}
else
{
lean_object* v_head_335_; lean_object* v_tail_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_347_; 
v_head_335_ = lean_ctor_get(v_x_334_, 0);
v_tail_336_ = lean_ctor_get(v_x_334_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_347_ == 0)
{
v___x_338_ = v_x_334_;
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_tail_336_);
lean_inc(v_head_335_);
lean_dec(v_x_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
lean_inc(v_x_332_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 5);
lean_ctor_set(v___x_338_, 1, v_x_332_);
lean_ctor_set(v___x_338_, 0, v_x_333_);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_x_333_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_x_332_);
v___x_341_ = v_reuseFailAlloc_346_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = l_String_quote(v_head_335_);
v___x_343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v_x_333_ = v___x_344_;
v_x_334_ = v_tail_336_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_dec(v_x_348_);
return v_x_349_;
}
else
{
lean_object* v_head_351_; lean_object* v_tail_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_363_; 
v_head_351_ = lean_ctor_get(v_x_350_, 0);
v_tail_352_ = lean_ctor_get(v_x_350_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_363_ == 0)
{
v___x_354_ = v_x_350_;
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_tail_352_);
lean_inc(v_head_351_);
lean_dec(v_x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
lean_inc(v_x_348_);
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 5);
lean_ctor_set(v___x_354_, 1, v_x_348_);
lean_ctor_set(v___x_354_, 0, v_x_349_);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_x_349_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_x_348_);
v___x_357_ = v_reuseFailAlloc_362_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = l_String_quote(v_head_351_);
v___x_359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_357_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(v_x_348_, v___x_360_, v_tail_352_);
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_object* v___x_366_; 
lean_dec(v_x_365_);
v___x_366_ = lean_box(0);
return v___x_366_;
}
else
{
lean_object* v_tail_367_; 
v_tail_367_ = lean_ctor_get(v_x_364_, 1);
if (lean_obj_tag(v_tail_367_) == 0)
{
lean_object* v_head_368_; lean_object* v___x_369_; 
lean_dec(v_x_365_);
v_head_368_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_head_368_);
lean_dec_ref(v_x_364_);
v___x_369_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_368_);
return v___x_369_;
}
else
{
lean_object* v_head_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_inc(v_tail_367_);
v_head_370_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_head_370_);
lean_dec_ref(v_x_364_);
v___x_371_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_370_);
v___x_372_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_365_, v___x_371_, v_tail_367_);
return v___x_372_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0));
v___x_379_ = lean_string_length(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3);
v___x_381_ = lean_nat_to_int(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = lean_array_get_size(v_xs_389_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_nat_dec_eq(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_393_ = lean_array_to_list(v_xs_389_);
v___x_394_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1));
v___x_395_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_393_, v___x_394_);
v___x_396_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4);
v___x_397_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_395_);
v___x_399_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6));
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Std_Format_fill(v___x_401_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v_xs_389_);
v___x_403_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8));
return v___x_403_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(11u);
v___x_414_ = lean_nat_to_int(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(14u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(16u);
v___x_433_ = lean_nat_to_int(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(9u);
v___x_441_ = lean_nat_to_int(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(13u);
v___x_448_ = lean_nat_to_int(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__29(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(6u);
v___x_456_ = lean_nat_to_int(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(12u);
v___x_464_ = lean_nat_to_int(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__39(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(19u);
v___x_472_ = lean_nat_to_int(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__46(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(21u);
v___x_483_ = lean_nat_to_int(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_487_){
_start:
{
lean_object* v_sysroot_488_; lean_object* v_githash_489_; lean_object* v_srcDir_490_; lean_object* v_leanLibDir_491_; lean_object* v_includeDir_492_; lean_object* v_systemLibDir_493_; lean_object* v_binDir_494_; lean_object* v_lean_495_; lean_object* v_leanir_496_; lean_object* v_leanc_497_; lean_object* v_leantar_498_; lean_object* v_sharedLib_499_; lean_object* v_initSharedLib_500_; lean_object* v_ar_501_; lean_object* v_cc_502_; uint8_t v_customCc_503_; lean_object* v_cFlags_504_; lean_object* v_linkStaticFlags_505_; lean_object* v_linkSharedFlags_506_; lean_object* v_ccFlags_507_; lean_object* v_ccLinkStaticFlags_508_; lean_object* v_ccLinkSharedFlags_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_sysroot_488_ = lean_ctor_get(v_x_487_, 0);
lean_inc_ref(v_sysroot_488_);
v_githash_489_ = lean_ctor_get(v_x_487_, 1);
lean_inc_ref(v_githash_489_);
v_srcDir_490_ = lean_ctor_get(v_x_487_, 2);
lean_inc_ref(v_srcDir_490_);
v_leanLibDir_491_ = lean_ctor_get(v_x_487_, 3);
lean_inc_ref(v_leanLibDir_491_);
v_includeDir_492_ = lean_ctor_get(v_x_487_, 4);
lean_inc_ref(v_includeDir_492_);
v_systemLibDir_493_ = lean_ctor_get(v_x_487_, 5);
lean_inc_ref(v_systemLibDir_493_);
v_binDir_494_ = lean_ctor_get(v_x_487_, 6);
lean_inc_ref(v_binDir_494_);
v_lean_495_ = lean_ctor_get(v_x_487_, 7);
lean_inc_ref(v_lean_495_);
v_leanir_496_ = lean_ctor_get(v_x_487_, 8);
lean_inc_ref(v_leanir_496_);
v_leanc_497_ = lean_ctor_get(v_x_487_, 9);
lean_inc_ref(v_leanc_497_);
v_leantar_498_ = lean_ctor_get(v_x_487_, 10);
lean_inc_ref(v_leantar_498_);
v_sharedLib_499_ = lean_ctor_get(v_x_487_, 11);
lean_inc_ref(v_sharedLib_499_);
v_initSharedLib_500_ = lean_ctor_get(v_x_487_, 12);
lean_inc_ref(v_initSharedLib_500_);
v_ar_501_ = lean_ctor_get(v_x_487_, 13);
lean_inc_ref(v_ar_501_);
v_cc_502_ = lean_ctor_get(v_x_487_, 14);
lean_inc_ref(v_cc_502_);
v_customCc_503_ = lean_ctor_get_uint8(v_x_487_, sizeof(void*)*21);
v_cFlags_504_ = lean_ctor_get(v_x_487_, 15);
lean_inc_ref(v_cFlags_504_);
v_linkStaticFlags_505_ = lean_ctor_get(v_x_487_, 16);
lean_inc_ref(v_linkStaticFlags_505_);
v_linkSharedFlags_506_ = lean_ctor_get(v_x_487_, 17);
lean_inc_ref(v_linkSharedFlags_506_);
v_ccFlags_507_ = lean_ctor_get(v_x_487_, 18);
lean_inc_ref(v_ccFlags_507_);
v_ccLinkStaticFlags_508_ = lean_ctor_get(v_x_487_, 19);
lean_inc_ref(v_ccLinkStaticFlags_508_);
v_ccLinkSharedFlags_509_ = lean_ctor_get(v_x_487_, 20);
lean_inc_ref(v_ccLinkSharedFlags_509_);
lean_dec_ref(v_x_487_);
v___x_510_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_511_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_512_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_515_ = l_String_quote(v_sysroot_488_);
v___x_516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_514_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v___x_513_);
v___x_519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_512_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_520_);
v___x_522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_511_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_box(1);
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_510_);
v___x_530_ = l_String_quote(v_githash_489_);
v___x_531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_512_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*1, v___x_520_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_529_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_523_);
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_525_);
v___x_537_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_510_);
v___x_540_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_541_ = l_String_quote(v_srcDir_490_);
v___x_542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_514_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Repr_addAppParen(v___x_543_, v___x_513_);
v___x_545_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_540_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*1, v___x_520_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_539_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_523_);
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_525_);
v___x_550_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___x_510_);
v___x_553_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_554_ = l_String_quote(v_leanLibDir_491_);
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_514_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Repr_addAppParen(v___x_556_, v___x_513_);
v___x_558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_553_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*1, v___x_520_);
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_552_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_523_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_525_);
v___x_563_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_510_);
v___x_566_ = l_String_quote(v_includeDir_492_);
v___x_567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_514_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Repr_addAppParen(v___x_568_, v___x_513_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_553_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*1, v___x_520_);
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_565_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_523_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_525_);
v___x_575_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_510_);
v___x_578_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_579_ = l_String_quote(v_systemLibDir_493_);
v___x_580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_514_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Repr_addAppParen(v___x_581_, v___x_513_);
v___x_583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_578_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*1, v___x_520_);
v___x_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_577_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_523_);
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_525_);
v___x_588_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_510_);
v___x_591_ = l_String_quote(v_binDir_494_);
v___x_592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
v___x_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_514_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Repr_addAppParen(v___x_593_, v___x_513_);
v___x_595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_540_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*1, v___x_520_);
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_590_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_523_);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_525_);
v___x_600_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_510_);
v___x_603_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_604_ = l_String_quote(v_lean_495_);
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_514_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Repr_addAppParen(v___x_606_, v___x_513_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_603_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_520_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_602_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_523_);
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_525_);
v___x_613_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_510_);
v___x_616_ = l_String_quote(v_leanir_496_);
v___x_617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
v___x_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_514_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Repr_addAppParen(v___x_618_, v___x_513_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_540_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*1, v___x_520_);
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_615_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_523_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_525_);
v___x_625_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_510_);
v___x_628_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_629_ = l_String_quote(v_leanc_497_);
v___x_630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_514_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Repr_addAppParen(v___x_631_, v___x_513_);
v___x_633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_628_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*1, v___x_520_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_627_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_523_);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_525_);
v___x_638_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_510_);
v___x_641_ = l_String_quote(v_leantar_498_);
v___x_642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_514_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Repr_addAppParen(v___x_643_, v___x_513_);
v___x_645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_512_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_520_);
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_640_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_523_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_525_);
v___x_650_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_510_);
v___x_653_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__24, &l_Lake_instReprLeanInstall_repr___redArg___closed__24_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24);
v___x_654_ = l_String_quote(v_sharedLib_499_);
v___x_655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_514_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Repr_addAppParen(v___x_656_, v___x_513_);
v___x_658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_653_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_520_);
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_652_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_523_);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_525_);
v___x_663_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_510_);
v___x_666_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_667_ = l_String_quote(v_initSharedLib_500_);
v___x_668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
v___x_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_514_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Repr_addAppParen(v___x_669_, v___x_513_);
v___x_671_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_666_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*1, v___x_520_);
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_665_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_523_);
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_525_);
v___x_676_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__28));
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_510_);
v___x_679_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__29, &l_Lake_instReprLeanInstall_repr___redArg___closed__29_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__29);
v___x_680_ = l_String_quote(v_ar_501_);
v___x_681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_514_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Repr_addAppParen(v___x_682_, v___x_513_);
v___x_684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_679_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*1, v___x_520_);
v___x_686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_678_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_523_);
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_525_);
v___x_689_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__31));
v___x_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_510_);
v___x_692_ = l_String_quote(v_cc_502_);
v___x_693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
v___x_694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_514_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_Repr_addAppParen(v___x_694_, v___x_513_);
v___x_696_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_679_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*1, v___x_520_);
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_691_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_523_);
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_525_);
v___x_701_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__33));
v___x_702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_510_);
v___x_704_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__34, &l_Lake_instReprLeanInstall_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__34);
v___x_705_ = l_Bool_repr___redArg(v_customCc_503_);
v___x_706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_520_);
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_703_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_523_);
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_525_);
v___x_711_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__36));
v___x_712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_510_);
v___x_714_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_cFlags_504_);
v___x_715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_540_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_520_);
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_713_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_523_);
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_525_);
v___x_720_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__38));
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_510_);
v___x_723_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__39, &l_Lake_instReprLeanInstall_repr___redArg___closed__39_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__39);
v___x_724_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkStaticFlags_505_);
v___x_725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*1, v___x_520_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_722_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_523_);
v___x_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_525_);
v___x_730_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__41));
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_510_);
v___x_733_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkSharedFlags_506_);
v___x_734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_723_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set_uint8(v___x_735_, sizeof(void*)*1, v___x_520_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_732_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_523_);
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_525_);
v___x_739_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__43));
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_510_);
v___x_742_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccFlags_507_);
v___x_743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_512_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*1, v___x_520_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_741_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_523_);
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_525_);
v___x_748_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__45));
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_510_);
v___x_751_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__46, &l_Lake_instReprLeanInstall_repr___redArg___closed__46_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__46);
v___x_752_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkStaticFlags_508_);
v___x_753_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_520_);
v___x_755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_750_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_523_);
v___x_757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_525_);
v___x_758_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__48));
v___x_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v___x_510_);
v___x_761_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkSharedFlags_509_);
v___x_762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_751_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*1, v___x_520_);
v___x_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_760_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_766_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_764_);
v___x_768_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_765_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*1, v___x_520_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_772_, lean_object* v_prec_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_775_, lean_object* v_prec_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lake_instReprLeanInstall_repr(v_x_775_, v_prec_776_);
lean_dec(v_prec_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_System_Platform_isWindows;
if (v___x_781_ == 0)
{
lean_object* v_leanLibDir_782_; lean_object* v_systemLibDir_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_leanLibDir_782_ = lean_ctor_get(v_self_780_, 3);
v_systemLibDir_783_ = lean_ctor_get(v_self_780_, 5);
v___x_784_ = lean_box(0);
lean_inc_ref(v_systemLibDir_783_);
v___x_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_785_, 0, v_systemLibDir_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
lean_inc_ref(v_leanLibDir_782_);
v___x_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_786_, 0, v_leanLibDir_782_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v_binDir_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_binDir_787_ = lean_ctor_get(v_self_780_, 6);
v___x_788_ = lean_box(0);
lean_inc_ref(v_binDir_787_);
v___x_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_789_, 0, v_binDir_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lake_LeanInstall_sharedLibPath(v_self_790_);
lean_dec_ref(v_self_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_792_){
_start:
{
uint8_t v_customCc_793_; 
v_customCc_793_ = lean_ctor_get_uint8(v_self_792_, sizeof(void*)*21);
if (v_customCc_793_ == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_box(0);
return v___x_794_;
}
else
{
lean_object* v_cc_795_; lean_object* v___x_796_; 
v_cc_795_ = lean_ctor_get(v_self_792_, 14);
lean_inc_ref(v_cc_795_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_cc_795_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_LeanInstall_leanCc_x3f(v_self_797_);
lean_dec_ref(v_self_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_799_, lean_object* v_self_800_){
_start:
{
if (v_shared_799_ == 0)
{
lean_object* v_ccLinkStaticFlags_801_; 
v_ccLinkStaticFlags_801_ = lean_ctor_get(v_self_800_, 19);
lean_inc_ref(v_ccLinkStaticFlags_801_);
return v_ccLinkStaticFlags_801_;
}
else
{
lean_object* v_ccLinkSharedFlags_802_; 
v_ccLinkSharedFlags_802_ = lean_ctor_get(v_self_800_, 20);
lean_inc_ref(v_ccLinkSharedFlags_802_);
return v_ccLinkSharedFlags_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_803_, lean_object* v_self_804_){
_start:
{
uint8_t v_shared_boxed_805_; lean_object* v_res_806_; 
v_shared_boxed_805_ = lean_unbox(v_shared_803_);
v_res_806_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_805_, v_self_804_);
lean_dec_ref(v_self_804_);
return v_res_806_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = l_System_FilePath_exeExtension;
v___x_809_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_810_ = l_System_FilePath_addExtension(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_811_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = l_Lake_instInhabitedDynlib_default;
v___x_813_ = l_System_instInhabitedFilePath_default;
v___x_814_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
lean_ctor_set(v___x_814_, 2, v___x_813_);
lean_ctor_set(v___x_814_, 3, v___x_813_);
lean_ctor_set(v___x_814_, 4, v___x_812_);
lean_ctor_set(v___x_814_, 5, v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
return v___x_815_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_825_){
_start:
{
lean_object* v_home_826_; lean_object* v_srcDir_827_; lean_object* v_binDir_828_; lean_object* v_libDir_829_; lean_object* v_sharedDynlib_830_; lean_object* v_lake_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_home_826_ = lean_ctor_get(v_x_825_, 0);
lean_inc_ref(v_home_826_);
v_srcDir_827_ = lean_ctor_get(v_x_825_, 1);
lean_inc_ref(v_srcDir_827_);
v_binDir_828_ = lean_ctor_get(v_x_825_, 2);
lean_inc_ref(v_binDir_828_);
v_libDir_829_ = lean_ctor_get(v_x_825_, 3);
lean_inc_ref(v_libDir_829_);
v_sharedDynlib_830_ = lean_ctor_get(v_x_825_, 4);
lean_inc_ref(v_sharedDynlib_830_);
v_lake_831_ = lean_ctor_get(v_x_825_, 5);
lean_inc_ref(v_lake_831_);
lean_dec_ref(v_x_825_);
v___x_832_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_833_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_834_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_837_ = l_String_quote(v_home_826_);
v___x_838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_836_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Repr_addAppParen(v___x_839_, v___x_835_);
v___x_841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_834_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = 0;
v___x_843_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v___x_842_);
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_833_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_box(1);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_832_);
v___x_852_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_853_ = l_String_quote(v_srcDir_827_);
v___x_854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_836_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Repr_addAppParen(v___x_855_, v___x_835_);
v___x_857_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_852_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*1, v___x_842_);
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_851_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_845_);
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_847_);
v___x_862_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_832_);
v___x_865_ = l_String_quote(v_binDir_828_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_836_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Repr_addAppParen(v___x_867_, v___x_835_);
v___x_869_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_852_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_842_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_864_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_845_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_847_);
v___x_874_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_832_);
v___x_877_ = l_String_quote(v_libDir_829_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_836_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Repr_addAppParen(v___x_879_, v___x_835_);
v___x_881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_852_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*1, v___x_842_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_876_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_845_);
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_847_);
v___x_886_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__3));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_832_);
v___x_889_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_890_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_830_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*1, v___x_842_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_888_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_845_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_847_);
v___x_896_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__4));
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_832_);
v___x_899_ = l_String_quote(v_lake_831_);
v___x_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_836_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Repr_addAppParen(v___x_901_, v___x_835_);
v___x_903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_834_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_842_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_898_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_907_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_905_);
v___x_909_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_842_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_913_, lean_object* v_prec_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_916_, lean_object* v_prec_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lake_instReprLakeInstall_repr(v_x_916_, v_prec_917_);
lean_dec(v_prec_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_921_){
_start:
{
lean_object* v_sharedDynlib_922_; lean_object* v_path_923_; 
v_sharedDynlib_922_ = lean_ctor_get(v_self_921_, 4);
v_path_923_ = lean_ctor_get(v_sharedDynlib_922_, 0);
lean_inc_ref(v_path_923_);
return v_path_923_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lake_LakeInstall_sharedLib(v_self_924_);
lean_dec_ref(v_self_924_);
return v_res_925_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_lib_932_; 
v___x_930_ = l_Lake_sharedLibExt;
v___x_931_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__2));
v_lib_932_ = lean_string_append(v___x_931_, v___x_930_);
return v_lib_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_933_){
_start:
{
lean_object* v_sysroot_934_; lean_object* v_srcDir_935_; lean_object* v_leanLibDir_936_; lean_object* v_binDir_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___y_941_; lean_object* v_lib_949_; uint8_t v___x_950_; 
v_sysroot_934_ = lean_ctor_get(v_lean_933_, 0);
lean_inc_ref(v_sysroot_934_);
v_srcDir_935_ = lean_ctor_get(v_lean_933_, 2);
lean_inc_ref(v_srcDir_935_);
v_leanLibDir_936_ = lean_ctor_get(v_lean_933_, 3);
lean_inc_ref(v_leanLibDir_936_);
v_binDir_937_ = lean_ctor_get(v_lean_933_, 6);
lean_inc_ref(v_binDir_937_);
lean_dec_ref(v_lean_933_);
v___x_938_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_939_ = l_System_FilePath_join(v_srcDir_935_, v___x_938_);
v_lib_949_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__3, &l_Lake_LakeInstall_ofLean___closed__3_once, _init_l_Lake_LakeInstall_ofLean___closed__3);
v___x_950_ = l_System_Platform_isWindows;
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_inc_ref(v_leanLibDir_936_);
v___x_951_ = l_System_FilePath_join(v_leanLibDir_936_, v_lib_949_);
v___y_941_ = v___x_951_;
goto v___jp_940_;
}
else
{
lean_object* v___x_952_; 
lean_inc_ref(v_binDir_937_);
v___x_952_ = l_System_FilePath_join(v_binDir_937_, v_lib_949_);
v___y_941_ = v___x_952_;
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_942_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_943_ = 0;
v___x_944_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_945_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_945_, 0, v___y_941_);
lean_ctor_set(v___x_945_, 1, v___x_942_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*3, v___x_943_);
v___x_946_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_937_);
v___x_947_ = l_System_FilePath_join(v_binDir_937_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_948_, 0, v_sysroot_934_);
lean_ctor_set(v___x_948_, 1, v___x_939_);
lean_ctor_set(v___x_948_, 2, v_binDir_937_);
lean_ctor_set(v___x_948_, 3, v_leanLibDir_936_);
lean_ctor_set(v___x_948_, 4, v___x_945_);
lean_ctor_set(v___x_948_, 5, v___x_947_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_958_ = lean_io_getenv(v___x_957_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_986_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_986_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_986_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_val_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_986_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___y_966_; 
v___x_963_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_964_ = lean_io_getenv(v___x_963_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_966_ = v___x_984_;
goto v___jp_965_;
}
else
{
lean_object* v_val_985_; 
v_val_985_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v___x_964_);
v___y_966_ = v_val_985_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_startInclusive_971_; lean_object* v_endExclusive_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_string_utf8_byte_size(v___y_966_);
lean_inc_ref(v___y_966_);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v___y_966_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = l_String_Slice_trimAscii(v___x_969_);
v_startInclusive_971_ = lean_ctor_get(v___x_970_, 1);
lean_inc(v_startInclusive_971_);
v_endExclusive_972_ = lean_ctor_get(v___x_970_, 2);
lean_inc(v_endExclusive_972_);
lean_dec_ref(v___x_970_);
v___x_973_ = lean_nat_sub(v_endExclusive_972_, v_startInclusive_971_);
lean_dec(v_startInclusive_971_);
lean_dec(v_endExclusive_972_);
v___x_974_ = lean_nat_dec_eq(v___x_973_, v___x_967_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_975_ = ((lean_object*)(l_Lake_leanExe___closed__0));
lean_inc_n(v_val_959_, 2);
v___x_976_ = l_System_FilePath_join(v_val_959_, v___x_975_);
v___x_977_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__2));
v___x_978_ = l_System_FilePath_join(v_val_959_, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_979_, 0, v_val_959_);
lean_ctor_set(v___x_979_, 1, v___y_966_);
lean_ctor_set(v___x_979_, 2, v___x_976_);
lean_ctor_set(v___x_979_, 3, v___x_978_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_979_);
v___x_981_ = v___x_961_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_983_; 
lean_dec_ref(v___y_966_);
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
v___x_983_ = lean_box(0);
return v___x_983_;
}
}
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v___x_958_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lake_findElanInstall_x3f();
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1001_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1002_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1006_ = 1;
v___x_1007_ = 0;
v___x_1008_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1008_, 0, v___x_1001_);
lean_ctor_set(v___x_1008_, 1, v_lean_999_);
lean_ctor_set(v___x_1008_, 2, v___x_1002_);
lean_ctor_set(v___x_1008_, 3, v___x_1003_);
lean_ctor_set(v___x_1008_, 4, v___x_1005_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*5, v___x_1006_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*5 + 1, v___x_1007_);
v___x_1009_ = l_IO_Process_output(v___x_1008_, v___x_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1028_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1028_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1028_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint32_t v_exitCode_1014_; lean_object* v_stdout_1015_; uint32_t v___x_1016_; uint8_t v___x_1017_; 
v_exitCode_1014_ = lean_ctor_get_uint32(v_a_1010_, sizeof(void*)*2);
v_stdout_1015_ = lean_ctor_get(v_a_1010_, 0);
lean_inc_ref(v_stdout_1015_);
lean_dec(v_a_1010_);
v___x_1016_ = 0;
v___x_1017_ = lean_uint32_dec_eq(v_exitCode_1014_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v_stdout_1015_);
lean_del_object(v___x_1012_);
return v___x_1003_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_str_1021_; lean_object* v_startInclusive_1022_; lean_object* v_endExclusive_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1018_ = lean_string_utf8_byte_size(v_stdout_1015_);
v___x_1019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1019_, 0, v_stdout_1015_);
lean_ctor_set(v___x_1019_, 1, v___x_1004_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
v___x_1020_ = l_String_Slice_trimAscii(v___x_1019_);
v_str_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_ref(v_str_1021_);
v_startInclusive_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_startInclusive_1022_);
v_endExclusive_1023_ = lean_ctor_get(v___x_1020_, 2);
lean_inc(v_endExclusive_1023_);
lean_dec_ref(v___x_1020_);
v___x_1024_ = lean_string_utf8_extract(v_str_1021_, v_startInclusive_1022_, v_endExclusive_1023_);
lean_dec(v_endExclusive_1023_);
lean_dec(v_startInclusive_1022_);
lean_dec_ref(v_str_1021_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1024_);
v___x_1026_ = v___x_1012_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_dec_ref(v___x_1009_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lake_findLeanSysroot_x3f(v_lean_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1039_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1040_ = l_Lake_leanExe(v_sysroot_1037_);
v___x_1041_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1045_ = 1;
v___x_1046_ = 0;
v___x_1047_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1047_, 0, v___x_1039_);
lean_ctor_set(v___x_1047_, 1, v___x_1040_);
lean_ctor_set(v___x_1047_, 2, v___x_1041_);
lean_ctor_set(v___x_1047_, 3, v___x_1042_);
lean_ctor_set(v___x_1047_, 4, v___x_1044_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5, v___x_1045_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*5 + 1, v___x_1046_);
v___x_1048_ = l_IO_Process_output(v___x_1047_, v___x_1042_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v_stdout_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_str_1054_; lean_object* v_startInclusive_1055_; lean_object* v_endExclusive_1056_; lean_object* v___x_1057_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref(v___x_1048_);
v_stdout_1050_ = lean_ctor_get(v_a_1049_, 0);
lean_inc_ref(v_stdout_1050_);
lean_dec(v_a_1049_);
v___x_1051_ = lean_string_utf8_byte_size(v_stdout_1050_);
v___x_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1052_, 0, v_stdout_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1043_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
v___x_1053_ = l_String_Slice_trimAscii(v___x_1052_);
v_str_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc_ref(v_str_1054_);
v_startInclusive_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_startInclusive_1055_);
v_endExclusive_1056_ = lean_ctor_get(v___x_1053_, 2);
lean_inc(v_endExclusive_1056_);
lean_dec_ref(v___x_1053_);
v___x_1057_ = lean_string_utf8_extract(v_str_1054_, v_startInclusive_1055_, v_endExclusive_1056_);
lean_dec(v_endExclusive_1056_);
lean_dec(v_startInclusive_1055_);
lean_dec_ref(v_str_1054_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; 
lean_dec_ref(v___x_1048_);
v___x_1058_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1064_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1067_ = lean_io_getenv(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 1)
{
lean_object* v_val_1068_; 
lean_dec_ref(v_sysroot_1064_);
v_val_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_val_1068_);
lean_dec_ref(v___x_1067_);
return v_val_1068_;
}
else
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
lean_dec(v___x_1067_);
v___x_1069_ = l_Lake_leanArExe(v_sysroot_1064_);
v___x_1070_ = l_System_FilePath_pathExists(v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec_ref(v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1072_ = lean_io_getenv(v___x_1071_);
if (lean_obj_tag(v___x_1072_) == 1)
{
lean_object* v_val_1073_; 
v_val_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1073_);
lean_dec_ref(v___x_1072_);
return v_val_1073_;
}
else
{
lean_object* v___x_1074_; 
lean_dec(v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__27));
return v___x_1074_;
}
}
else
{
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1078_, lean_object* v_i_1079_, lean_object* v_cc_1080_){
_start:
{
lean_object* v_sysroot_1081_; lean_object* v_githash_1082_; lean_object* v_srcDir_1083_; lean_object* v_leanLibDir_1084_; lean_object* v_includeDir_1085_; lean_object* v_systemLibDir_1086_; lean_object* v_binDir_1087_; lean_object* v_lean_1088_; lean_object* v_leanir_1089_; lean_object* v_leanc_1090_; lean_object* v_leantar_1091_; lean_object* v_sharedLib_1092_; lean_object* v_initSharedLib_1093_; lean_object* v_ar_1094_; lean_object* v_cFlags_1095_; lean_object* v_linkStaticFlags_1096_; lean_object* v_linkSharedFlags_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1110_; 
v_sysroot_1081_ = lean_ctor_get(v_i_1079_, 0);
v_githash_1082_ = lean_ctor_get(v_i_1079_, 1);
v_srcDir_1083_ = lean_ctor_get(v_i_1079_, 2);
v_leanLibDir_1084_ = lean_ctor_get(v_i_1079_, 3);
v_includeDir_1085_ = lean_ctor_get(v_i_1079_, 4);
v_systemLibDir_1086_ = lean_ctor_get(v_i_1079_, 5);
v_binDir_1087_ = lean_ctor_get(v_i_1079_, 6);
v_lean_1088_ = lean_ctor_get(v_i_1079_, 7);
v_leanir_1089_ = lean_ctor_get(v_i_1079_, 8);
v_leanc_1090_ = lean_ctor_get(v_i_1079_, 9);
v_leantar_1091_ = lean_ctor_get(v_i_1079_, 10);
v_sharedLib_1092_ = lean_ctor_get(v_i_1079_, 11);
v_initSharedLib_1093_ = lean_ctor_get(v_i_1079_, 12);
v_ar_1094_ = lean_ctor_get(v_i_1079_, 13);
v_cFlags_1095_ = lean_ctor_get(v_i_1079_, 15);
v_linkStaticFlags_1096_ = lean_ctor_get(v_i_1079_, 16);
v_linkSharedFlags_1097_ = lean_ctor_get(v_i_1079_, 17);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_i_1079_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; 
v_unused_1111_ = lean_ctor_get(v_i_1079_, 20);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_i_1079_, 19);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_i_1079_, 18);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_i_1079_, 14);
lean_dec(v_unused_1114_);
v___x_1099_ = v_i_1079_;
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_linkSharedFlags_1097_);
lean_inc(v_linkStaticFlags_1096_);
lean_inc(v_cFlags_1095_);
lean_inc(v_ar_1094_);
lean_inc(v_initSharedLib_1093_);
lean_inc(v_sharedLib_1092_);
lean_inc(v_leantar_1091_);
lean_inc(v_leanc_1090_);
lean_inc(v_leanir_1089_);
lean_inc(v_lean_1088_);
lean_inc(v_binDir_1087_);
lean_inc(v_systemLibDir_1086_);
lean_inc(v_includeDir_1085_);
lean_inc(v_leanLibDir_1084_);
lean_inc(v_srcDir_1083_);
lean_inc(v_githash_1082_);
lean_inc(v_sysroot_1081_);
lean_dec(v_i_1079_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_ccLinkFlags_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_ccLinkFlags_1101_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1078_);
v___x_1102_ = 0;
v___x_1103_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1078_);
lean_inc_ref(v_cFlags_1095_);
v___x_1104_ = l_Array_append___redArg(v_cFlags_1095_, v___x_1103_);
lean_dec_ref(v___x_1103_);
lean_inc_ref(v_ccLinkFlags_1101_);
v___x_1105_ = l_Array_append___redArg(v_ccLinkFlags_1101_, v_linkStaticFlags_1096_);
v___x_1106_ = l_Array_append___redArg(v_ccLinkFlags_1101_, v_linkSharedFlags_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 20, v___x_1106_);
lean_ctor_set(v___x_1099_, 19, v___x_1105_);
lean_ctor_set(v___x_1099_, 18, v___x_1104_);
lean_ctor_set(v___x_1099_, 14, v_cc_1080_);
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_sysroot_1081_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_githash_1082_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_srcDir_1083_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_leanLibDir_1084_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_includeDir_1085_);
lean_ctor_set(v_reuseFailAlloc_1109_, 5, v_systemLibDir_1086_);
lean_ctor_set(v_reuseFailAlloc_1109_, 6, v_binDir_1087_);
lean_ctor_set(v_reuseFailAlloc_1109_, 7, v_lean_1088_);
lean_ctor_set(v_reuseFailAlloc_1109_, 8, v_leanir_1089_);
lean_ctor_set(v_reuseFailAlloc_1109_, 9, v_leanc_1090_);
lean_ctor_set(v_reuseFailAlloc_1109_, 10, v_leantar_1091_);
lean_ctor_set(v_reuseFailAlloc_1109_, 11, v_sharedLib_1092_);
lean_ctor_set(v_reuseFailAlloc_1109_, 12, v_initSharedLib_1093_);
lean_ctor_set(v_reuseFailAlloc_1109_, 13, v_ar_1094_);
lean_ctor_set(v_reuseFailAlloc_1109_, 14, v_cc_1080_);
lean_ctor_set(v_reuseFailAlloc_1109_, 15, v_cFlags_1095_);
lean_ctor_set(v_reuseFailAlloc_1109_, 16, v_linkStaticFlags_1096_);
lean_ctor_set(v_reuseFailAlloc_1109_, 17, v_linkSharedFlags_1097_);
lean_ctor_set(v_reuseFailAlloc_1109_, 18, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1109_, 19, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1109_, 20, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*21, v___x_1102_);
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1115_, lean_object* v_i_1116_, lean_object* v_cc_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1115_, v_i_1116_, v_cc_1117_);
lean_dec_ref(v_sysroot_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1119_, lean_object* v_cc_1120_){
_start:
{
lean_object* v_sysroot_1121_; lean_object* v_githash_1122_; lean_object* v_srcDir_1123_; lean_object* v_leanLibDir_1124_; lean_object* v_includeDir_1125_; lean_object* v_systemLibDir_1126_; lean_object* v_binDir_1127_; lean_object* v_lean_1128_; lean_object* v_leanir_1129_; lean_object* v_leanc_1130_; lean_object* v_leantar_1131_; lean_object* v_sharedLib_1132_; lean_object* v_initSharedLib_1133_; lean_object* v_ar_1134_; uint8_t v_customCc_1135_; lean_object* v_cFlags_1136_; lean_object* v_linkStaticFlags_1137_; lean_object* v_linkSharedFlags_1138_; lean_object* v_ccFlags_1139_; lean_object* v_ccLinkStaticFlags_1140_; lean_object* v_ccLinkSharedFlags_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_sysroot_1121_ = lean_ctor_get(v_i_1119_, 0);
v_githash_1122_ = lean_ctor_get(v_i_1119_, 1);
v_srcDir_1123_ = lean_ctor_get(v_i_1119_, 2);
v_leanLibDir_1124_ = lean_ctor_get(v_i_1119_, 3);
v_includeDir_1125_ = lean_ctor_get(v_i_1119_, 4);
v_systemLibDir_1126_ = lean_ctor_get(v_i_1119_, 5);
v_binDir_1127_ = lean_ctor_get(v_i_1119_, 6);
v_lean_1128_ = lean_ctor_get(v_i_1119_, 7);
v_leanir_1129_ = lean_ctor_get(v_i_1119_, 8);
v_leanc_1130_ = lean_ctor_get(v_i_1119_, 9);
v_leantar_1131_ = lean_ctor_get(v_i_1119_, 10);
v_sharedLib_1132_ = lean_ctor_get(v_i_1119_, 11);
v_initSharedLib_1133_ = lean_ctor_get(v_i_1119_, 12);
v_ar_1134_ = lean_ctor_get(v_i_1119_, 13);
v_customCc_1135_ = lean_ctor_get_uint8(v_i_1119_, sizeof(void*)*21);
v_cFlags_1136_ = lean_ctor_get(v_i_1119_, 15);
v_linkStaticFlags_1137_ = lean_ctor_get(v_i_1119_, 16);
v_linkSharedFlags_1138_ = lean_ctor_get(v_i_1119_, 17);
v_ccFlags_1139_ = lean_ctor_get(v_i_1119_, 18);
v_ccLinkStaticFlags_1140_ = lean_ctor_get(v_i_1119_, 19);
v_ccLinkSharedFlags_1141_ = lean_ctor_get(v_i_1119_, 20);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_i_1119_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_i_1119_, 14);
lean_dec(v_unused_1149_);
v___x_1143_ = v_i_1119_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1141_);
lean_inc(v_ccLinkStaticFlags_1140_);
lean_inc(v_ccFlags_1139_);
lean_inc(v_linkSharedFlags_1138_);
lean_inc(v_linkStaticFlags_1137_);
lean_inc(v_cFlags_1136_);
lean_inc(v_ar_1134_);
lean_inc(v_initSharedLib_1133_);
lean_inc(v_sharedLib_1132_);
lean_inc(v_leantar_1131_);
lean_inc(v_leanc_1130_);
lean_inc(v_leanir_1129_);
lean_inc(v_lean_1128_);
lean_inc(v_binDir_1127_);
lean_inc(v_systemLibDir_1126_);
lean_inc(v_includeDir_1125_);
lean_inc(v_leanLibDir_1124_);
lean_inc(v_srcDir_1123_);
lean_inc(v_githash_1122_);
lean_inc(v_sysroot_1121_);
lean_dec(v_i_1119_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 14, v_cc_1120_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_sysroot_1121_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_githash_1122_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_srcDir_1123_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_leanLibDir_1124_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_includeDir_1125_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_systemLibDir_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v_binDir_1127_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_lean_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 8, v_leanir_1129_);
lean_ctor_set(v_reuseFailAlloc_1147_, 9, v_leanc_1130_);
lean_ctor_set(v_reuseFailAlloc_1147_, 10, v_leantar_1131_);
lean_ctor_set(v_reuseFailAlloc_1147_, 11, v_sharedLib_1132_);
lean_ctor_set(v_reuseFailAlloc_1147_, 12, v_initSharedLib_1133_);
lean_ctor_set(v_reuseFailAlloc_1147_, 13, v_ar_1134_);
lean_ctor_set(v_reuseFailAlloc_1147_, 14, v_cc_1120_);
lean_ctor_set(v_reuseFailAlloc_1147_, 15, v_cFlags_1136_);
lean_ctor_set(v_reuseFailAlloc_1147_, 16, v_linkStaticFlags_1137_);
lean_ctor_set(v_reuseFailAlloc_1147_, 17, v_linkSharedFlags_1138_);
lean_ctor_set(v_reuseFailAlloc_1147_, 18, v_ccFlags_1139_);
lean_ctor_set(v_reuseFailAlloc_1147_, 19, v_ccLinkStaticFlags_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 20, v_ccLinkSharedFlags_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*21, v_customCc_1135_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1152_, lean_object* v_i_1153_){
_start:
{
lean_object* v_cc_1156_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1187_ = lean_io_getenv(v___x_1186_);
if (lean_obj_tag(v___x_1187_) == 1)
{
lean_object* v_val_1188_; 
lean_dec_ref(v_sysroot_1152_);
v_val_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_val_1188_);
lean_dec_ref(v___x_1187_);
v_cc_1156_ = v_val_1188_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
lean_dec(v___x_1187_);
lean_inc_ref(v_sysroot_1152_);
v___x_1189_ = l_Lake_leanCcExe(v_sysroot_1152_);
v___x_1190_ = l_System_FilePath_pathExists(v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v___x_1189_);
lean_dec_ref(v_sysroot_1152_);
v___x_1191_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1192_ = lean_io_getenv(v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 1)
{
lean_object* v_val_1193_; 
v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref(v___x_1192_);
v_cc_1156_ = v_val_1193_;
goto v___jp_1155_;
}
else
{
lean_object* v_sysroot_1194_; lean_object* v_githash_1195_; lean_object* v_srcDir_1196_; lean_object* v_leanLibDir_1197_; lean_object* v_includeDir_1198_; lean_object* v_systemLibDir_1199_; lean_object* v_binDir_1200_; lean_object* v_lean_1201_; lean_object* v_leanir_1202_; lean_object* v_leanc_1203_; lean_object* v_leantar_1204_; lean_object* v_sharedLib_1205_; lean_object* v_initSharedLib_1206_; lean_object* v_ar_1207_; uint8_t v_customCc_1208_; lean_object* v_cFlags_1209_; lean_object* v_linkStaticFlags_1210_; lean_object* v_linkSharedFlags_1211_; lean_object* v_ccFlags_1212_; lean_object* v_ccLinkStaticFlags_1213_; lean_object* v_ccLinkSharedFlags_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v___x_1192_);
v_sysroot_1194_ = lean_ctor_get(v_i_1153_, 0);
v_githash_1195_ = lean_ctor_get(v_i_1153_, 1);
v_srcDir_1196_ = lean_ctor_get(v_i_1153_, 2);
v_leanLibDir_1197_ = lean_ctor_get(v_i_1153_, 3);
v_includeDir_1198_ = lean_ctor_get(v_i_1153_, 4);
v_systemLibDir_1199_ = lean_ctor_get(v_i_1153_, 5);
v_binDir_1200_ = lean_ctor_get(v_i_1153_, 6);
v_lean_1201_ = lean_ctor_get(v_i_1153_, 7);
v_leanir_1202_ = lean_ctor_get(v_i_1153_, 8);
v_leanc_1203_ = lean_ctor_get(v_i_1153_, 9);
v_leantar_1204_ = lean_ctor_get(v_i_1153_, 10);
v_sharedLib_1205_ = lean_ctor_get(v_i_1153_, 11);
v_initSharedLib_1206_ = lean_ctor_get(v_i_1153_, 12);
v_ar_1207_ = lean_ctor_get(v_i_1153_, 13);
v_customCc_1208_ = lean_ctor_get_uint8(v_i_1153_, sizeof(void*)*21);
v_cFlags_1209_ = lean_ctor_get(v_i_1153_, 15);
v_linkStaticFlags_1210_ = lean_ctor_get(v_i_1153_, 16);
v_linkSharedFlags_1211_ = lean_ctor_get(v_i_1153_, 17);
v_ccFlags_1212_ = lean_ctor_get(v_i_1153_, 18);
v_ccLinkStaticFlags_1213_ = lean_ctor_get(v_i_1153_, 19);
v_ccLinkSharedFlags_1214_ = lean_ctor_get(v_i_1153_, 20);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_i_1153_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_i_1153_, 14);
lean_dec(v_unused_1223_);
v___x_1216_ = v_i_1153_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1214_);
lean_inc(v_ccLinkStaticFlags_1213_);
lean_inc(v_ccFlags_1212_);
lean_inc(v_linkSharedFlags_1211_);
lean_inc(v_linkStaticFlags_1210_);
lean_inc(v_cFlags_1209_);
lean_inc(v_ar_1207_);
lean_inc(v_initSharedLib_1206_);
lean_inc(v_sharedLib_1205_);
lean_inc(v_leantar_1204_);
lean_inc(v_leanc_1203_);
lean_inc(v_leanir_1202_);
lean_inc(v_lean_1201_);
lean_inc(v_binDir_1200_);
lean_inc(v_systemLibDir_1199_);
lean_inc(v_includeDir_1198_);
lean_inc(v_leanLibDir_1197_);
lean_inc(v_srcDir_1196_);
lean_inc(v_githash_1195_);
lean_inc(v_sysroot_1194_);
lean_dec(v_i_1153_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 14, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_sysroot_1194_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_githash_1195_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_srcDir_1196_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_leanLibDir_1197_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_includeDir_1198_);
lean_ctor_set(v_reuseFailAlloc_1221_, 5, v_systemLibDir_1199_);
lean_ctor_set(v_reuseFailAlloc_1221_, 6, v_binDir_1200_);
lean_ctor_set(v_reuseFailAlloc_1221_, 7, v_lean_1201_);
lean_ctor_set(v_reuseFailAlloc_1221_, 8, v_leanir_1202_);
lean_ctor_set(v_reuseFailAlloc_1221_, 9, v_leanc_1203_);
lean_ctor_set(v_reuseFailAlloc_1221_, 10, v_leantar_1204_);
lean_ctor_set(v_reuseFailAlloc_1221_, 11, v_sharedLib_1205_);
lean_ctor_set(v_reuseFailAlloc_1221_, 12, v_initSharedLib_1206_);
lean_ctor_set(v_reuseFailAlloc_1221_, 13, v_ar_1207_);
lean_ctor_set(v_reuseFailAlloc_1221_, 14, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 15, v_cFlags_1209_);
lean_ctor_set(v_reuseFailAlloc_1221_, 16, v_linkStaticFlags_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 17, v_linkSharedFlags_1211_);
lean_ctor_set(v_reuseFailAlloc_1221_, 18, v_ccFlags_1212_);
lean_ctor_set(v_reuseFailAlloc_1221_, 19, v_ccLinkStaticFlags_1213_);
lean_ctor_set(v_reuseFailAlloc_1221_, 20, v_ccLinkSharedFlags_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, sizeof(void*)*21, v_customCc_1208_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1152_, v_i_1153_, v___x_1189_);
lean_dec_ref(v_sysroot_1152_);
return v___x_1224_;
}
}
v___jp_1155_:
{
lean_object* v_sysroot_1157_; lean_object* v_githash_1158_; lean_object* v_srcDir_1159_; lean_object* v_leanLibDir_1160_; lean_object* v_includeDir_1161_; lean_object* v_systemLibDir_1162_; lean_object* v_binDir_1163_; lean_object* v_lean_1164_; lean_object* v_leanir_1165_; lean_object* v_leanc_1166_; lean_object* v_leantar_1167_; lean_object* v_sharedLib_1168_; lean_object* v_initSharedLib_1169_; lean_object* v_ar_1170_; uint8_t v_customCc_1171_; lean_object* v_cFlags_1172_; lean_object* v_linkStaticFlags_1173_; lean_object* v_linkSharedFlags_1174_; lean_object* v_ccFlags_1175_; lean_object* v_ccLinkStaticFlags_1176_; lean_object* v_ccLinkSharedFlags_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_sysroot_1157_ = lean_ctor_get(v_i_1153_, 0);
v_githash_1158_ = lean_ctor_get(v_i_1153_, 1);
v_srcDir_1159_ = lean_ctor_get(v_i_1153_, 2);
v_leanLibDir_1160_ = lean_ctor_get(v_i_1153_, 3);
v_includeDir_1161_ = lean_ctor_get(v_i_1153_, 4);
v_systemLibDir_1162_ = lean_ctor_get(v_i_1153_, 5);
v_binDir_1163_ = lean_ctor_get(v_i_1153_, 6);
v_lean_1164_ = lean_ctor_get(v_i_1153_, 7);
v_leanir_1165_ = lean_ctor_get(v_i_1153_, 8);
v_leanc_1166_ = lean_ctor_get(v_i_1153_, 9);
v_leantar_1167_ = lean_ctor_get(v_i_1153_, 10);
v_sharedLib_1168_ = lean_ctor_get(v_i_1153_, 11);
v_initSharedLib_1169_ = lean_ctor_get(v_i_1153_, 12);
v_ar_1170_ = lean_ctor_get(v_i_1153_, 13);
v_customCc_1171_ = lean_ctor_get_uint8(v_i_1153_, sizeof(void*)*21);
v_cFlags_1172_ = lean_ctor_get(v_i_1153_, 15);
v_linkStaticFlags_1173_ = lean_ctor_get(v_i_1153_, 16);
v_linkSharedFlags_1174_ = lean_ctor_get(v_i_1153_, 17);
v_ccFlags_1175_ = lean_ctor_get(v_i_1153_, 18);
v_ccLinkStaticFlags_1176_ = lean_ctor_get(v_i_1153_, 19);
v_ccLinkSharedFlags_1177_ = lean_ctor_get(v_i_1153_, 20);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_i_1153_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v_i_1153_, 14);
lean_dec(v_unused_1185_);
v___x_1179_ = v_i_1153_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1177_);
lean_inc(v_ccLinkStaticFlags_1176_);
lean_inc(v_ccFlags_1175_);
lean_inc(v_linkSharedFlags_1174_);
lean_inc(v_linkStaticFlags_1173_);
lean_inc(v_cFlags_1172_);
lean_inc(v_ar_1170_);
lean_inc(v_initSharedLib_1169_);
lean_inc(v_sharedLib_1168_);
lean_inc(v_leantar_1167_);
lean_inc(v_leanc_1166_);
lean_inc(v_leanir_1165_);
lean_inc(v_lean_1164_);
lean_inc(v_binDir_1163_);
lean_inc(v_systemLibDir_1162_);
lean_inc(v_includeDir_1161_);
lean_inc(v_leanLibDir_1160_);
lean_inc(v_srcDir_1159_);
lean_inc(v_githash_1158_);
lean_inc(v_sysroot_1157_);
lean_dec(v_i_1153_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 14, v_cc_1156_);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_sysroot_1157_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_githash_1158_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_srcDir_1159_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_leanLibDir_1160_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_includeDir_1161_);
lean_ctor_set(v_reuseFailAlloc_1183_, 5, v_systemLibDir_1162_);
lean_ctor_set(v_reuseFailAlloc_1183_, 6, v_binDir_1163_);
lean_ctor_set(v_reuseFailAlloc_1183_, 7, v_lean_1164_);
lean_ctor_set(v_reuseFailAlloc_1183_, 8, v_leanir_1165_);
lean_ctor_set(v_reuseFailAlloc_1183_, 9, v_leanc_1166_);
lean_ctor_set(v_reuseFailAlloc_1183_, 10, v_leantar_1167_);
lean_ctor_set(v_reuseFailAlloc_1183_, 11, v_sharedLib_1168_);
lean_ctor_set(v_reuseFailAlloc_1183_, 12, v_initSharedLib_1169_);
lean_ctor_set(v_reuseFailAlloc_1183_, 13, v_ar_1170_);
lean_ctor_set(v_reuseFailAlloc_1183_, 14, v_cc_1156_);
lean_ctor_set(v_reuseFailAlloc_1183_, 15, v_cFlags_1172_);
lean_ctor_set(v_reuseFailAlloc_1183_, 16, v_linkStaticFlags_1173_);
lean_ctor_set(v_reuseFailAlloc_1183_, 17, v_linkSharedFlags_1174_);
lean_ctor_set(v_reuseFailAlloc_1183_, 18, v_ccFlags_1175_);
lean_ctor_set(v_reuseFailAlloc_1183_, 19, v_ccLinkStaticFlags_1176_);
lean_ctor_set(v_reuseFailAlloc_1183_, 20, v_ccLinkSharedFlags_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1183_, sizeof(void*)*21, v_customCc_1171_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1225_, lean_object* v_i_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1225_, v_i_1226_);
return v_res_1228_;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__3(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__2));
v___x_1233_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_1234_ = lean_array_push(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__4(void){
_start:
{
uint8_t v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = 1;
v___x_1236_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lake_LeanInstall_get___closed__5(void){
_start:
{
uint8_t v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = 0;
v___x_1238_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1239_, uint8_t v_collocated_1240_){
_start:
{
lean_object* v_githash_1243_; 
if (v_collocated_1240_ == 0)
{
lean_object* v___x_1272_; 
lean_inc_ref(v_sysroot_1239_);
v___x_1272_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1239_);
v_githash_1243_ = v___x_1272_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_githash;
v_githash_1243_ = v___x_1273_;
goto v___jp_1242_;
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_inc_ref_n(v_sysroot_1239_, 11);
v___x_1244_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1239_);
v___x_1245_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__0));
v___x_1246_ = l_System_FilePath_join(v_sysroot_1239_, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1248_ = l_System_FilePath_join(v___x_1246_, v___x_1247_);
v___x_1249_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1250_ = l_System_FilePath_join(v_sysroot_1239_, v___x_1249_);
lean_inc_ref(v___x_1250_);
v___x_1251_ = l_System_FilePath_join(v___x_1250_, v___x_1247_);
v___x_1252_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__1));
v___x_1253_ = l_System_FilePath_join(v_sysroot_1239_, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1255_ = l_System_FilePath_join(v_sysroot_1239_, v___x_1254_);
v___x_1256_ = l_Lake_leanExe(v_sysroot_1239_);
v___x_1257_ = l_Lake_leanirExe(v_sysroot_1239_);
v___x_1258_ = l_Lake_leancExe(v_sysroot_1239_);
v___x_1259_ = l_Lake_leantarExe(v_sysroot_1239_);
v___x_1260_ = l_Lake_leanSharedLibDir(v_sysroot_1239_);
v___x_1261_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1260_);
v___x_1262_ = l_System_FilePath_join(v___x_1260_, v___x_1261_);
v___x_1263_ = l_Lake_initSharedLib;
v___x_1264_ = l_System_FilePath_join(v___x_1260_, v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_1266_ = 1;
v___x_1267_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__3, &l_Lake_LeanInstall_get___closed__3_once, _init_l_Lake_LeanInstall_get___closed__3);
v___x_1268_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__4, &l_Lake_LeanInstall_get___closed__4_once, _init_l_Lake_LeanInstall_get___closed__4);
v___x_1269_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__5, &l_Lake_LeanInstall_get___closed__5_once, _init_l_Lake_LeanInstall_get___closed__5);
v___x_1270_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1270_, 0, v_sysroot_1239_);
lean_ctor_set(v___x_1270_, 1, v_githash_1243_);
lean_ctor_set(v___x_1270_, 2, v___x_1248_);
lean_ctor_set(v___x_1270_, 3, v___x_1251_);
lean_ctor_set(v___x_1270_, 4, v___x_1253_);
lean_ctor_set(v___x_1270_, 5, v___x_1250_);
lean_ctor_set(v___x_1270_, 6, v___x_1255_);
lean_ctor_set(v___x_1270_, 7, v___x_1256_);
lean_ctor_set(v___x_1270_, 8, v___x_1257_);
lean_ctor_set(v___x_1270_, 9, v___x_1258_);
lean_ctor_set(v___x_1270_, 10, v___x_1259_);
lean_ctor_set(v___x_1270_, 11, v___x_1262_);
lean_ctor_set(v___x_1270_, 12, v___x_1264_);
lean_ctor_set(v___x_1270_, 13, v___x_1244_);
lean_ctor_set(v___x_1270_, 14, v___x_1265_);
lean_ctor_set(v___x_1270_, 15, v___x_1267_);
lean_ctor_set(v___x_1270_, 16, v___x_1268_);
lean_ctor_set(v___x_1270_, 17, v___x_1269_);
lean_ctor_set(v___x_1270_, 18, v___x_1267_);
lean_ctor_set(v___x_1270_, 19, v___x_1268_);
lean_ctor_set(v___x_1270_, 20, v___x_1269_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*21, v___x_1266_);
v___x_1271_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1239_, v___x_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1274_, lean_object* v_collocated_1275_, lean_object* v_a_1276_){
_start:
{
uint8_t v_collocated_boxed_1277_; lean_object* v_res_1278_; 
v_collocated_boxed_1277_ = lean_unbox(v_collocated_1275_);
v_res_1278_ = l_Lake_LeanInstall_get(v_sysroot_1274_, v_collocated_boxed_1277_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lake_findLeanSysroot_x3f(v_lean_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = 0;
v___x_1288_ = l_Lake_LeanInstall_get(v_val_1283_, v___x_1287_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_io_app_path();
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = l_System_FilePath_parent(v_a_1300_);
if (lean_obj_tag(v___x_1301_) == 1)
{
lean_object* v_val_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_val_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc_n(v_val_1302_, 2);
lean_dec_ref(v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1304_ = l_System_FilePath_join(v_val_1302_, v___x_1303_);
v___x_1305_ = l_System_FilePath_exeExtension;
v___x_1306_ = l_System_FilePath_addExtension(v___x_1304_, v___x_1305_);
v___x_1307_ = l_System_FilePath_pathExists(v___x_1306_);
lean_dec_ref(v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_val_1302_);
goto v___jp_1297_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = l_System_FilePath_parent(v_val_1302_);
return v___x_1308_;
}
}
else
{
lean_dec(v___x_1301_);
goto v___jp_1297_;
}
}
else
{
lean_dec_ref(v___x_1299_);
goto v___jp_1297_;
}
v___jp_1297_:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_box(0);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_System_FilePath_parent(v_lake_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
return v___x_1312_;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; 
v_val_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref(v___x_1312_);
v___x_1314_ = l_System_FilePath_parent(v_val_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
return v___x_1314_;
}
else
{
lean_object* v_val_1315_; lean_object* v___x_1316_; 
v_val_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_val_1315_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = l_System_FilePath_parent(v_val_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
return v___x_1316_;
}
else
{
lean_object* v_val_1317_; lean_object* v___x_1318_; 
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = l_System_FilePath_parent(v_val_1317_);
return v___x_1318_;
}
}
}
}
}
static lean_object* _init_l_Lake_getLakeInstall_x3f___closed__1(void){
_start:
{
uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = 0;
v___x_1321_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1322_ = l_Lake_nameToSharedLib(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1324_){
_start:
{
lean_object* v___x_1326_; 
lean_inc_ref(v_lake_1324_);
v___x_1326_ = l_Lake_lakeBuildHome_x3f(v_lake_1324_);
if (lean_obj_tag(v___x_1326_) == 1)
{
lean_object* v_val_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1351_; 
v_val_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1351_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_val_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1351_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_lake_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1331_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1327_, 2);
v___x_1332_ = l_System_FilePath_join(v_val_1327_, v___x_1331_);
v___x_1333_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1332_);
v___x_1334_ = l_System_FilePath_join(v___x_1332_, v___x_1333_);
v___x_1335_ = l_Lake_defaultLeanLibDir;
v___x_1336_ = l_System_FilePath_join(v___x_1332_, v___x_1335_);
v___x_1337_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1338_ = 0;
v___x_1339_ = lean_obj_once(&l_Lake_getLakeInstall_x3f___closed__1, &l_Lake_getLakeInstall_x3f___closed__1_once, _init_l_Lake_getLakeInstall_x3f___closed__1);
lean_inc_ref_n(v___x_1336_, 2);
v___x_1340_ = l_System_FilePath_join(v___x_1336_, v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1342_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1337_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*3, v___x_1338_);
v_lake_1343_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1343_, 0, v_val_1327_);
lean_ctor_set(v_lake_1343_, 1, v_val_1327_);
lean_ctor_set(v_lake_1343_, 2, v___x_1334_);
lean_ctor_set(v_lake_1343_, 3, v___x_1336_);
lean_ctor_set(v_lake_1343_, 4, v___x_1342_);
lean_ctor_set(v_lake_1343_, 5, v_lake_1324_);
v___x_1344_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__2));
v___x_1345_ = l_System_FilePath_join(v___x_1336_, v___x_1344_);
v___x_1346_ = l_System_FilePath_pathExists(v___x_1345_);
lean_dec_ref(v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref(v_lake_1343_);
lean_del_object(v___x_1329_);
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
else
{
lean_object* v___x_1349_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_lake_1343_);
v___x_1349_ = v___x_1329_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_lake_1343_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v___x_1352_; 
lean_dec(v___x_1326_);
lean_dec_ref(v_lake_1324_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lake_getLakeInstall_x3f(v_lake_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1360_ = lean_io_getenv(v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = 0;
v___x_1366_ = l_Lake_LeanInstall_get(v_val_1361_, v___x_1365_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_lean_1374_; 
lean_dec(v___x_1360_);
v___x_1371_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1372_ = lean_io_getenv(v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 1)
{
lean_object* v_val_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v_startInclusive_1392_; lean_object* v_endExclusive_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_val_1387_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_n(v_val_1387_, 2);
lean_dec_ref(v___x_1372_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_string_utf8_byte_size(v_val_1387_);
v___x_1390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1390_, 0, v_val_1387_);
lean_ctor_set(v___x_1390_, 1, v___x_1388_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = l_String_Slice_trimAscii(v___x_1390_);
v_startInclusive_1392_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_startInclusive_1392_);
v_endExclusive_1393_ = lean_ctor_get(v___x_1391_, 2);
lean_inc(v_endExclusive_1393_);
lean_dec_ref(v___x_1391_);
v___x_1394_ = lean_nat_sub(v_endExclusive_1393_, v_startInclusive_1392_);
lean_dec(v_startInclusive_1392_);
lean_dec(v_endExclusive_1393_);
v___x_1395_ = lean_nat_dec_eq(v___x_1394_, v___x_1388_);
lean_dec(v___x_1394_);
if (v___x_1395_ == 0)
{
v_lean_1374_ = v_val_1387_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1396_; 
lean_dec(v_val_1387_);
v___x_1396_ = lean_box(0);
return v___x_1396_;
}
}
else
{
lean_object* v___x_1397_; 
lean_dec(v___x_1372_);
v___x_1397_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v_lean_1374_ = v___x_1397_;
goto v___jp_1373_;
}
v___jp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lake_findLeanSysroot_x3f(v_lean_1374_);
if (lean_obj_tag(v___x_1375_) == 1)
{
lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1385_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = 0;
v___x_1381_ = l_Lake_LeanInstall_get(v_val_1376_, v___x_1380_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1381_);
v___x_1383_ = v___x_1378_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_object* v___x_1386_; 
lean_dec(v___x_1375_);
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lake_findLeanInstall_x3f();
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_io_app_path();
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lake_getLakeInstall_x3f(v_a_1430_);
if (lean_obj_tag(v___x_1431_) == 1)
{
return v___x_1431_;
}
else
{
lean_dec(v___x_1431_);
goto v___jp_1402_;
}
}
else
{
lean_dec_ref(v___x_1429_);
goto v___jp_1402_;
}
v___jp_1402_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1404_ = lean_io_getenv(v___x_1403_);
if (lean_obj_tag(v___x_1404_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1427_; 
v_val_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1427_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_val_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1427_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1409_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1405_, 2);
v___x_1410_ = l_System_FilePath_join(v_val_1405_, v___x_1409_);
v___x_1411_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1410_);
v___x_1412_ = l_System_FilePath_join(v___x_1410_, v___x_1411_);
v___x_1413_ = l_Lake_defaultLeanLibDir;
v___x_1414_ = l_System_FilePath_join(v___x_1410_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1416_ = 0;
v___x_1417_ = lean_obj_once(&l_Lake_getLakeInstall_x3f___closed__1, &l_Lake_getLakeInstall_x3f___closed__1_once, _init_l_Lake_getLakeInstall_x3f___closed__1);
lean_inc_ref(v___x_1414_);
v___x_1418_ = l_System_FilePath_join(v___x_1414_, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1415_);
lean_ctor_set(v___x_1420_, 2, v___x_1419_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*3, v___x_1416_);
v___x_1421_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1412_);
v___x_1422_ = l_System_FilePath_join(v___x_1412_, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1423_, 0, v_val_1405_);
lean_ctor_set(v___x_1423_, 1, v_val_1405_);
lean_ctor_set(v___x_1423_, 2, v___x_1412_);
lean_ctor_set(v___x_1423_, 3, v___x_1414_);
lean_ctor_set(v___x_1423_, 4, v___x_1420_);
lean_ctor_set(v___x_1423_, 5, v___x_1422_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1423_);
v___x_1425_ = v___x_1407_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v___x_1428_; 
lean_dec(v___x_1404_);
v___x_1428_ = lean_box(0);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lake_findLakeInstall_x3f();
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = l_Lake_findElanInstall_x3f();
v___x_1437_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1437_) == 1)
{
lean_object* v_val_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1498_; 
v_val_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1498_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_val_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1498_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1443_ = lean_io_getenv(v___x_1442_);
if (lean_obj_tag(v___x_1443_) == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1455_; 
v_val_1454_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_val_1454_);
lean_dec_ref(v___x_1443_);
v___x_1455_ = l_Lake_envToBool_x3f(v_val_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v_val_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1497_; 
v_val_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1497_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_val_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1497_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_unbox(v_val_1456_);
if (v___x_1460_ == 0)
{
lean_del_object(v___x_1458_);
lean_dec(v_val_1456_);
goto v___jp_1444_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_del_object(v___x_1440_);
v___x_1461_ = ((lean_object*)(l_Lake_toolchain2Dir___closed__0));
v___x_1462_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__0));
lean_inc_n(v_val_1438_, 9);
v___x_1463_ = l_System_FilePath_join(v_val_1438_, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Lake_leanExe___closed__1));
v___x_1465_ = l_System_FilePath_join(v___x_1463_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1467_ = l_System_FilePath_join(v_val_1438_, v___x_1466_);
lean_inc_ref(v___x_1467_);
v___x_1468_ = l_System_FilePath_join(v___x_1467_, v___x_1464_);
v___x_1469_ = ((lean_object*)(l_Lake_LeanInstall_get___closed__1));
v___x_1470_ = l_System_FilePath_join(v_val_1438_, v___x_1469_);
v___x_1471_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1472_ = l_System_FilePath_join(v_val_1438_, v___x_1471_);
v___x_1473_ = l_Lake_leanExe(v_val_1438_);
v___x_1474_ = l_Lake_leanirExe(v_val_1438_);
v___x_1475_ = l_Lake_leancExe(v_val_1438_);
v___x_1476_ = l_Lake_leantarExe(v_val_1438_);
v___x_1477_ = l_Lake_leanSharedLibDir(v_val_1438_);
v___x_1478_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1477_);
v___x_1479_ = l_System_FilePath_join(v___x_1477_, v___x_1478_);
v___x_1480_ = l_Lake_initSharedLib;
v___x_1481_ = l_System_FilePath_join(v___x_1477_, v___x_1480_);
v___x_1482_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__27));
v___x_1483_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_1484_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__3, &l_Lake_LeanInstall_get___closed__3_once, _init_l_Lake_LeanInstall_get___closed__3);
v___x_1485_ = lean_unbox(v_val_1456_);
v___x_1486_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lake_LeanInstall_get___closed__5, &l_Lake_LeanInstall_get___closed__5_once, _init_l_Lake_LeanInstall_get___closed__5);
lean_inc_ref(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1488_, 0, v_val_1438_);
lean_ctor_set(v___x_1488_, 1, v___x_1461_);
lean_ctor_set(v___x_1488_, 2, v___x_1465_);
lean_ctor_set(v___x_1488_, 3, v___x_1468_);
lean_ctor_set(v___x_1488_, 4, v___x_1470_);
lean_ctor_set(v___x_1488_, 5, v___x_1467_);
lean_ctor_set(v___x_1488_, 6, v___x_1472_);
lean_ctor_set(v___x_1488_, 7, v___x_1473_);
lean_ctor_set(v___x_1488_, 8, v___x_1474_);
lean_ctor_set(v___x_1488_, 9, v___x_1475_);
lean_ctor_set(v___x_1488_, 10, v___x_1476_);
lean_ctor_set(v___x_1488_, 11, v___x_1479_);
lean_ctor_set(v___x_1488_, 12, v___x_1481_);
lean_ctor_set(v___x_1488_, 13, v___x_1482_);
lean_ctor_set(v___x_1488_, 14, v___x_1483_);
lean_ctor_set(v___x_1488_, 15, v___x_1484_);
lean_ctor_set(v___x_1488_, 16, v___x_1486_);
lean_ctor_set(v___x_1488_, 17, v___x_1487_);
lean_ctor_set(v___x_1488_, 18, v___x_1484_);
lean_ctor_set(v___x_1488_, 19, v___x_1486_);
lean_ctor_set(v___x_1488_, 20, v___x_1487_);
v___x_1489_ = lean_unbox(v_val_1456_);
lean_dec(v_val_1456_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*21, v___x_1489_);
v___x_1490_ = l_Lake_findLeanInstall_x3f();
v___x_1491_ = l_Lake_LakeInstall_ofLean(v___x_1488_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1491_);
v___x_1493_ = v___x_1458_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1436_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
return v___x_1495_;
}
}
}
}
}
v___jp_1444_:
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1445_ = 1;
v___x_1446_ = l_Lake_LeanInstall_get(v_val_1438_, v___x_1445_);
lean_inc_ref(v___x_1446_);
v___x_1447_ = l_Lake_LakeInstall_ofLean(v___x_1446_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1446_);
v___x_1449_ = v___x_1440_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1446_);
v___x_1449_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1447_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1436_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
return v___x_1452_;
}
}
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v___x_1437_);
v___x_1499_ = l_Lake_findLeanInstall_x3f();
v___x_1500_ = l_Lake_findLakeInstall_x3f();
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1436_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lake_findInstall_x3f();
return v_res_1504_;
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
