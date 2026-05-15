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
extern lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
extern lean_object* l_Lake_sharedLibExt;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
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
extern lean_object* l_Lake_defaultLeanLibDir;
extern lean_object* l_Lake_defaultBuildDir;
extern lean_object* l_Lake_defaultBinDir;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_app_path();
lean_object* l_System_FilePath_parent(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__13;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ar"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__14 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__14_value;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "cc"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__15 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__15_value;
static const lean_string_object l_Lake_instInhabitedLeanInstall_default___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "-Wno-unused-command-line-argument"};
static const lean_object* l_Lake_instInhabitedLeanInstall_default___closed__16 = (const lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__16_value;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__17;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__18;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__19;
static lean_once_cell_t l_Lake_instInhabitedLeanInstall_default___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLeanInstall_default___closed__20;
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
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__14_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__27 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__27_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__28;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanInstall_default___closed__15_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__29 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__29_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "customCc"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__30 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__31 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__31_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__32;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__33 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__33_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__34 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__34_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__35 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__36 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__36_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__37;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "linkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__38 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__38_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__39 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__39_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ccFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__41_value;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkStaticFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__43 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__43_value;
static lean_once_cell_t l_Lake_instReprLeanInstall_repr___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__44;
static const lean_string_object l_Lake_instReprLeanInstall_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ccLinkSharedFlags"};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lake_instReprLeanInstall_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__45_value)}};
static const lean_object* l_Lake_instReprLeanInstall_repr___redArg___closed__46 = (const lean_object*)&l_Lake_instReprLeanInstall_repr___redArg___closed__46_value;
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
static const lean_array_object l_Lake_instInhabitedLakeInstall_default___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLakeInstall_default___closed__6 = (const lean_object*)&l_Lake_instInhabitedLakeInstall_default___closed__6_value;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__7;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__8;
static lean_once_cell_t l_Lake_instInhabitedLakeInstall_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedLakeInstall_default___closed__9;
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
static const lean_string_object l_Lake_LakeInstall_ofLean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libLake_shared."};
static const lean_object* l_Lake_LakeInstall_ofLean___closed__1 = (const lean_object*)&l_Lake_LakeInstall_ofLean___closed__1_value;
static lean_once_cell_t l_Lake_LakeInstall_ofLean___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeInstall_ofLean___closed__2;
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
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_92_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_93_ = l_System_FilePath_join(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_96_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_97_ = l_System_FilePath_join(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__5(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__4, &l_Lake_instInhabitedElanInstall_default___closed__4_once, _init_l_Lake_instInhabitedElanInstall_default___closed__4);
v___x_99_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_100_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
lean_ctor_set(v___x_101_, 2, v___x_99_);
lean_ctor_set(v___x_101_, 3, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__5, &l_Lake_instInhabitedElanInstall_default___closed__5_once, _init_l_Lake_instInhabitedElanInstall_default___closed__5);
return v___x_102_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall(void){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lake_instInhabitedElanInstall_default;
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_nat_to_int(v_a_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(8u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(10u);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(17u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__0));
v___x_142_ = lean_string_length(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__21, &l_Lake_instReprElanInstall_repr___redArg___closed__21_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__21);
v___x_144_ = lean_nat_to_int(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* v_x_149_){
_start:
{
lean_object* v_home_150_; lean_object* v_elan_151_; lean_object* v_binDir_152_; lean_object* v_toolchainsDir_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_home_150_ = lean_ctor_get(v_x_149_, 0);
lean_inc_ref(v_home_150_);
v_elan_151_ = lean_ctor_get(v_x_149_, 1);
lean_inc_ref(v_elan_151_);
v_binDir_152_ = lean_ctor_get(v_x_149_, 2);
lean_inc_ref(v_binDir_152_);
v_toolchainsDir_153_ = lean_ctor_get(v_x_149_, 3);
lean_inc_ref(v_toolchainsDir_153_);
lean_dec_ref(v_x_149_);
v___x_154_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_155_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_156_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_159_ = l_String_quote(v_home_150_);
v___x_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_158_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Repr_addAppParen(v___x_161_, v___x_157_);
v___x_163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_156_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = 0;
v___x_165_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*1, v___x_164_);
v___x_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_155_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_box(1);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__13));
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_154_);
v___x_174_ = l_String_quote(v_elan_151_);
v___x_175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_158_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Repr_addAppParen(v___x_176_, v___x_157_);
v___x_178_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_156_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_164_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_173_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_167_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_169_);
v___x_183_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_154_);
v___x_186_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_187_ = l_String_quote(v_binDir_152_);
v___x_188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_158_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = l_Repr_addAppParen(v___x_189_, v___x_157_);
v___x_191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_186_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_164_);
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_185_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_167_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_169_);
v___x_196_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__18));
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_154_);
v___x_199_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_200_ = l_String_quote(v_toolchainsDir_153_);
v___x_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_158_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Repr_addAppParen(v___x_202_, v___x_157_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_199_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_164_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_198_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_208_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_206_);
v___x_210_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_207_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_164_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* v_x_214_, lean_object* v_prec_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lake_instReprElanInstall_repr___redArg(v_x_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_instReprElanInstall_repr(v_x_217_, v_prec_218_);
lean_dec(v_prec_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* v_toolchain_224_, lean_object* v_acc_225_, lean_object* v_pos_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_string_utf8_at_end(v_toolchain_224_, v_pos_226_);
if (v___x_227_ == 0)
{
uint32_t v_c_228_; lean_object* v_pos_x27_229_; uint32_t v___x_230_; uint8_t v___x_231_; 
v_c_228_ = lean_string_utf8_get_fast(v_toolchain_224_, v_pos_226_);
v_pos_x27_229_ = lean_string_utf8_next_fast(v_toolchain_224_, v_pos_226_);
lean_dec(v_pos_226_);
v___x_230_ = 47;
v___x_231_ = lean_uint32_dec_eq(v_c_228_, v___x_230_);
if (v___x_231_ == 0)
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 58;
v___x_233_ = lean_uint32_dec_eq(v_c_228_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_string_push(v_acc_225_, v_c_228_);
v_acc_225_ = v___x_234_;
v_pos_226_ = v_pos_x27_229_;
goto _start;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0));
v___x_237_ = lean_string_append(v_acc_225_, v___x_236_);
v_acc_225_ = v___x_237_;
v_pos_226_ = v_pos_x27_229_;
goto _start;
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1));
v___x_240_ = lean_string_append(v_acc_225_, v___x_239_);
v_acc_225_ = v___x_240_;
v_pos_226_ = v_pos_x27_229_;
goto _start;
}
}
else
{
lean_dec(v_pos_226_);
return v_acc_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* v_toolchain_242_, lean_object* v_acc_243_, lean_object* v_pos_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_242_, v_acc_243_, v_pos_244_);
lean_dec_ref(v_toolchain_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* v_toolchain_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_246_, v___x_247_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* v_toolchain_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_toolchain2Dir(v_toolchain_250_);
lean_dec_ref(v_toolchain_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* v_toolchain_252_, lean_object* v_elan_253_){
_start:
{
lean_object* v_toolchainsDir_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_toolchainsDir_254_ = lean_ctor_get(v_elan_253_, 3);
lean_inc_ref(v_toolchainsDir_254_);
lean_dec_ref(v_elan_253_);
v___x_255_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_252_, v___x_255_, v___x_256_);
v___x_258_ = l_System_FilePath_join(v_toolchainsDir_254_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* v_toolchain_259_, lean_object* v_elan_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_259_, v_elan_260_);
lean_dec_ref(v_toolchain_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* v_sysroot_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_264_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_265_ = l_System_FilePath_join(v_sysroot_263_, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_267_ = l_System_FilePath_join(v___x_265_, v___x_266_);
v___x_268_ = l_System_FilePath_exeExtension;
v___x_269_ = l_System_FilePath_addExtension(v___x_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object* v_sysroot_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_272_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_273_ = l_System_FilePath_join(v_sysroot_271_, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lake_leanirExe___closed__0));
v___x_275_ = l_System_FilePath_join(v___x_273_, v___x_274_);
v___x_276_ = l_System_FilePath_exeExtension;
v___x_277_ = l_System_FilePath_addExtension(v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_281_ = l_System_FilePath_join(v_sysroot_279_, v___x_280_);
v___x_282_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_283_ = l_System_FilePath_join(v___x_281_, v___x_282_);
v___x_284_ = l_System_FilePath_exeExtension;
v___x_285_ = l_System_FilePath_addExtension(v___x_283_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_288_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_289_ = l_System_FilePath_join(v_sysroot_287_, v___x_288_);
v___x_290_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_291_ = l_System_FilePath_join(v___x_289_, v___x_290_);
v___x_292_ = l_System_FilePath_exeExtension;
v___x_293_ = l_System_FilePath_addExtension(v___x_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_296_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_297_ = l_System_FilePath_join(v_sysroot_295_, v___x_296_);
v___x_298_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_299_ = l_System_FilePath_join(v___x_297_, v___x_298_);
v___x_300_ = l_System_FilePath_exeExtension;
v___x_301_ = l_System_FilePath_addExtension(v___x_299_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_304_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_305_ = l_System_FilePath_join(v_sysroot_303_, v___x_304_);
v___x_306_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_307_ = l_System_FilePath_join(v___x_305_, v___x_306_);
v___x_308_ = l_System_FilePath_exeExtension;
v___x_309_ = l_System_FilePath_addExtension(v___x_307_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = l_System_Platform_isWindows;
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_314_ = l_System_FilePath_join(v_sysroot_311_, v___x_313_);
v___x_315_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_316_ = l_System_FilePath_join(v___x_314_, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_318_ = l_System_FilePath_join(v_sysroot_311_, v___x_317_);
return v___x_318_;
}
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = l_Lake_sharedLibExt;
v___x_321_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_322_ = l_System_FilePath_addExtension(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_323_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = l_Lake_sharedLibExt;
v___x_326_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_327_ = l_System_FilePath_addExtension(v___x_326_, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_328_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_331_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_332_ = l_System_FilePath_join(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_334_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
v___x_335_ = l_System_FilePath_join(v___x_334_, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_337_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_338_ = l_System_FilePath_join(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_340_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_341_ = l_System_FilePath_join(v___x_340_, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_344_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_345_ = l_System_FilePath_join(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__7(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_347_ = l_Lake_leanExe(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__8(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_349_ = l_Lake_leanirExe(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__9(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_351_ = l_Lake_leancExe(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__10(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_353_ = l_Lake_leantarExe(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__11(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_355_ = l_Lake_leanSharedLibDir(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__12(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = l_Lake_leanSharedLib;
v___x_357_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_358_ = l_System_FilePath_join(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__13(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = l_Lake_initSharedLib;
v___x_360_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_361_ = l_System_FilePath_join(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__17(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__16));
v___x_366_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_367_ = lean_array_push(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__18(void){
_start:
{
uint8_t v___x_368_; lean_object* v___x_369_; 
v___x_368_ = 1;
v___x_369_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__19(void){
_start:
{
uint8_t v___x_370_; lean_object* v___x_371_; 
v___x_370_ = 0;
v___x_371_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__20(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_372_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
v___x_373_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_374_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_375_ = 1;
v___x_376_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_377_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_378_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__13, &l_Lake_instInhabitedLeanInstall_default___closed__13_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__13);
v___x_379_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__12, &l_Lake_instInhabitedLeanInstall_default___closed__12_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__12);
v___x_380_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__10, &l_Lake_instInhabitedLeanInstall_default___closed__10_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__10);
v___x_381_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__9, &l_Lake_instInhabitedLeanInstall_default___closed__9_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__9);
v___x_382_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__8, &l_Lake_instInhabitedLeanInstall_default___closed__8_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__8);
v___x_383_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__7, &l_Lake_instInhabitedLeanInstall_default___closed__7_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__7);
v___x_384_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_385_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_386_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
v___x_387_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_388_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__2, &l_Lake_instInhabitedLeanInstall_default___closed__2_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__2);
v___x_389_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_390_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
lean_ctor_set(v___x_390_, 2, v___x_388_);
lean_ctor_set(v___x_390_, 3, v___x_387_);
lean_ctor_set(v___x_390_, 4, v___x_386_);
lean_ctor_set(v___x_390_, 5, v___x_385_);
lean_ctor_set(v___x_390_, 6, v___x_384_);
lean_ctor_set(v___x_390_, 7, v___x_383_);
lean_ctor_set(v___x_390_, 8, v___x_382_);
lean_ctor_set(v___x_390_, 9, v___x_381_);
lean_ctor_set(v___x_390_, 10, v___x_380_);
lean_ctor_set(v___x_390_, 11, v___x_379_);
lean_ctor_set(v___x_390_, 12, v___x_378_);
lean_ctor_set(v___x_390_, 13, v___x_377_);
lean_ctor_set(v___x_390_, 14, v___x_376_);
lean_ctor_set(v___x_390_, 15, v___x_374_);
lean_ctor_set(v___x_390_, 16, v___x_373_);
lean_ctor_set(v___x_390_, 17, v___x_372_);
lean_ctor_set(v___x_390_, 18, v___x_374_);
lean_ctor_set(v___x_390_, 19, v___x_373_);
lean_ctor_set(v___x_390_, 20, v___x_372_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*21, v___x_375_);
return v___x_390_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__20, &l_Lake_instInhabitedLeanInstall_default___closed__20_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__20);
return v___x_391_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(lean_object* v___y_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = l_String_quote(v___y_393_);
v___x_395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_dec(v_x_396_);
return v_x_397_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v_head_399_ = lean_ctor_get(v_x_398_, 0);
v_tail_400_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v_x_398_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_tail_400_);
lean_inc(v_head_399_);
lean_dec(v_x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
lean_inc(v_x_396_);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 5);
lean_ctor_set(v___x_402_, 1, v_x_396_);
lean_ctor_set(v___x_402_, 0, v_x_397_);
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_x_397_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_x_396_);
v___x_405_ = v_reuseFailAlloc_410_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = l_String_quote(v_head_399_);
v___x_407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v_x_397_ = v___x_408_;
v_x_398_ = v_tail_400_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
lean_dec(v_x_412_);
return v_x_413_;
}
else
{
lean_object* v_head_415_; lean_object* v_tail_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
v_head_415_ = lean_ctor_get(v_x_414_, 0);
v_tail_416_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_427_ == 0)
{
v___x_418_ = v_x_414_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_tail_416_);
lean_inc(v_head_415_);
lean_dec(v_x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
lean_inc(v_x_412_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v_x_412_);
lean_ctor_set(v___x_418_, 0, v_x_413_);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_x_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_x_412_);
v___x_421_ = v_reuseFailAlloc_426_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = l_String_quote(v_head_415_);
v___x_423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___x_424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(v_x_412_, v___x_424_, v_tail_416_);
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v___x_430_; 
lean_dec(v_x_429_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v_tail_431_; 
v_tail_431_ = lean_ctor_get(v_x_428_, 1);
if (lean_obj_tag(v_tail_431_) == 0)
{
lean_object* v_head_432_; lean_object* v___x_433_; 
lean_dec(v_x_429_);
v_head_432_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_head_432_);
lean_dec_ref(v_x_428_);
v___x_433_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_432_);
return v___x_433_;
}
else
{
lean_object* v_head_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_inc(v_tail_431_);
v_head_434_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_head_434_);
lean_dec_ref(v_x_428_);
v___x_435_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_434_);
v___x_436_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_429_, v___x_435_, v_tail_431_);
return v___x_436_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0));
v___x_443_ = lean_string_length(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3);
v___x_445_ = lean_nat_to_int(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_array_get_size(v_xs_453_);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_nat_dec_eq(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_457_ = lean_array_to_list(v_xs_453_);
v___x_458_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1));
v___x_459_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_457_, v___x_458_);
v___x_460_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4);
v___x_461_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5));
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_459_);
v___x_463_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6));
v___x_464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_460_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Std_Format_fill(v___x_465_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
lean_dec_ref(v_xs_453_);
v___x_467_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8));
return v___x_467_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(11u);
v___x_478_ = lean_nat_to_int(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(14u);
v___x_489_ = lean_nat_to_int(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(16u);
v___x_497_ = lean_nat_to_int(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(9u);
v___x_505_ = lean_nat_to_int(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(13u);
v___x_512_ = lean_nat_to_int(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(6u);
v___x_519_ = lean_nat_to_int(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(12u);
v___x_526_ = lean_nat_to_int(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(19u);
v___x_534_ = lean_nat_to_int(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(21u);
v___x_545_ = lean_nat_to_int(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_549_){
_start:
{
lean_object* v_sysroot_550_; lean_object* v_githash_551_; lean_object* v_srcDir_552_; lean_object* v_leanLibDir_553_; lean_object* v_includeDir_554_; lean_object* v_systemLibDir_555_; lean_object* v_binDir_556_; lean_object* v_lean_557_; lean_object* v_leanir_558_; lean_object* v_leanc_559_; lean_object* v_leantar_560_; lean_object* v_sharedLib_561_; lean_object* v_initSharedLib_562_; lean_object* v_ar_563_; lean_object* v_cc_564_; uint8_t v_customCc_565_; lean_object* v_cFlags_566_; lean_object* v_linkStaticFlags_567_; lean_object* v_linkSharedFlags_568_; lean_object* v_ccFlags_569_; lean_object* v_ccLinkStaticFlags_570_; lean_object* v_ccLinkSharedFlags_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_sysroot_550_ = lean_ctor_get(v_x_549_, 0);
lean_inc_ref(v_sysroot_550_);
v_githash_551_ = lean_ctor_get(v_x_549_, 1);
lean_inc_ref(v_githash_551_);
v_srcDir_552_ = lean_ctor_get(v_x_549_, 2);
lean_inc_ref(v_srcDir_552_);
v_leanLibDir_553_ = lean_ctor_get(v_x_549_, 3);
lean_inc_ref(v_leanLibDir_553_);
v_includeDir_554_ = lean_ctor_get(v_x_549_, 4);
lean_inc_ref(v_includeDir_554_);
v_systemLibDir_555_ = lean_ctor_get(v_x_549_, 5);
lean_inc_ref(v_systemLibDir_555_);
v_binDir_556_ = lean_ctor_get(v_x_549_, 6);
lean_inc_ref(v_binDir_556_);
v_lean_557_ = lean_ctor_get(v_x_549_, 7);
lean_inc_ref(v_lean_557_);
v_leanir_558_ = lean_ctor_get(v_x_549_, 8);
lean_inc_ref(v_leanir_558_);
v_leanc_559_ = lean_ctor_get(v_x_549_, 9);
lean_inc_ref(v_leanc_559_);
v_leantar_560_ = lean_ctor_get(v_x_549_, 10);
lean_inc_ref(v_leantar_560_);
v_sharedLib_561_ = lean_ctor_get(v_x_549_, 11);
lean_inc_ref(v_sharedLib_561_);
v_initSharedLib_562_ = lean_ctor_get(v_x_549_, 12);
lean_inc_ref(v_initSharedLib_562_);
v_ar_563_ = lean_ctor_get(v_x_549_, 13);
lean_inc_ref(v_ar_563_);
v_cc_564_ = lean_ctor_get(v_x_549_, 14);
lean_inc_ref(v_cc_564_);
v_customCc_565_ = lean_ctor_get_uint8(v_x_549_, sizeof(void*)*21);
v_cFlags_566_ = lean_ctor_get(v_x_549_, 15);
lean_inc_ref(v_cFlags_566_);
v_linkStaticFlags_567_ = lean_ctor_get(v_x_549_, 16);
lean_inc_ref(v_linkStaticFlags_567_);
v_linkSharedFlags_568_ = lean_ctor_get(v_x_549_, 17);
lean_inc_ref(v_linkSharedFlags_568_);
v_ccFlags_569_ = lean_ctor_get(v_x_549_, 18);
lean_inc_ref(v_ccFlags_569_);
v_ccLinkStaticFlags_570_ = lean_ctor_get(v_x_549_, 19);
lean_inc_ref(v_ccLinkStaticFlags_570_);
v_ccLinkSharedFlags_571_ = lean_ctor_get(v_x_549_, 20);
lean_inc_ref(v_ccLinkSharedFlags_571_);
lean_dec_ref(v_x_549_);
v___x_572_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_573_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_574_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_577_ = l_String_quote(v_sysroot_550_);
v___x_578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_576_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Repr_addAppParen(v___x_579_, v___x_575_);
v___x_581_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_574_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = 0;
v___x_583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_582_);
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_573_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_box(1);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_572_);
v___x_592_ = l_String_quote(v_githash_551_);
v___x_593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_574_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*1, v___x_582_);
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_591_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_585_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_587_);
v___x_599_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_572_);
v___x_602_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_603_ = l_String_quote(v_srcDir_552_);
v___x_604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_576_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Repr_addAppParen(v___x_605_, v___x_575_);
v___x_607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_602_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_582_);
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_601_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_585_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_587_);
v___x_612_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_572_);
v___x_615_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_616_ = l_String_quote(v_leanLibDir_553_);
v___x_617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
v___x_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_576_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Repr_addAppParen(v___x_618_, v___x_575_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_615_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*1, v___x_582_);
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_614_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_585_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_587_);
v___x_625_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_572_);
v___x_628_ = l_String_quote(v_includeDir_554_);
v___x_629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_576_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Repr_addAppParen(v___x_630_, v___x_575_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_615_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_582_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_627_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_585_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_587_);
v___x_637_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_572_);
v___x_640_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_641_ = l_String_quote(v_systemLibDir_555_);
v___x_642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_576_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Repr_addAppParen(v___x_643_, v___x_575_);
v___x_645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_640_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_582_);
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_639_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_585_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_587_);
v___x_650_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_572_);
v___x_653_ = l_String_quote(v_binDir_556_);
v___x_654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___x_655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_576_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Repr_addAppParen(v___x_655_, v___x_575_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_602_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*1, v___x_582_);
v___x_659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_652_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_585_);
v___x_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_587_);
v___x_662_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_572_);
v___x_665_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_666_ = l_String_quote(v_lean_557_);
v___x_667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_576_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Repr_addAppParen(v___x_668_, v___x_575_);
v___x_670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_665_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*1, v___x_582_);
v___x_672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_664_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_585_);
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_587_);
v___x_675_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_572_);
v___x_678_ = l_String_quote(v_leanir_558_);
v___x_679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_576_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = l_Repr_addAppParen(v___x_680_, v___x_575_);
v___x_682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_602_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v___x_582_);
v___x_684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_677_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_585_);
v___x_686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_587_);
v___x_687_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_572_);
v___x_690_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_691_ = l_String_quote(v_leanc_559_);
v___x_692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
v___x_693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_576_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Repr_addAppParen(v___x_693_, v___x_575_);
v___x_695_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_690_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*1, v___x_582_);
v___x_697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_689_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_585_);
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_587_);
v___x_700_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_572_);
v___x_703_ = l_String_quote(v_leantar_560_);
v___x_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_576_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Repr_addAppParen(v___x_705_, v___x_575_);
v___x_707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_574_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*1, v___x_582_);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_702_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_585_);
v___x_711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_587_);
v___x_712_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_572_);
v___x_715_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__24, &l_Lake_instReprLeanInstall_repr___redArg___closed__24_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24);
v___x_716_ = l_String_quote(v_sharedLib_561_);
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_576_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Repr_addAppParen(v___x_718_, v___x_575_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_715_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*1, v___x_582_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_714_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_585_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_587_);
v___x_725_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_572_);
v___x_728_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_729_ = l_String_quote(v_initSharedLib_562_);
v___x_730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
v___x_731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_576_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Repr_addAppParen(v___x_731_, v___x_575_);
v___x_733_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_728_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*1, v___x_582_);
v___x_735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_727_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_585_);
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_587_);
v___x_738_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__27));
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_572_);
v___x_741_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__28, &l_Lake_instReprLeanInstall_repr___redArg___closed__28_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28);
v___x_742_ = l_String_quote(v_ar_563_);
v___x_743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_576_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Repr_addAppParen(v___x_744_, v___x_575_);
v___x_746_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_741_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_582_);
v___x_748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_740_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_585_);
v___x_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_587_);
v___x_751_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__29));
v___x_752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_572_);
v___x_754_ = l_String_quote(v_cc_564_);
v___x_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v___x_756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_576_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Repr_addAppParen(v___x_756_, v___x_575_);
v___x_758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_741_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*1, v___x_582_);
v___x_760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_753_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_585_);
v___x_762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_587_);
v___x_763_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__31));
v___x_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_572_);
v___x_766_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__32, &l_Lake_instReprLeanInstall_repr___redArg___closed__32_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32);
v___x_767_ = l_Bool_repr___redArg(v_customCc_565_);
v___x_768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_582_);
v___x_770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_765_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_585_);
v___x_772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_587_);
v___x_773_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__34));
v___x_774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_572_);
v___x_776_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_cFlags_566_);
v___x_777_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_602_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_778_, sizeof(void*)*1, v___x_582_);
v___x_779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_775_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_585_);
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_587_);
v___x_782_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__36));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_572_);
v___x_785_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__37, &l_Lake_instReprLeanInstall_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37);
v___x_786_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkStaticFlags_567_);
v___x_787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*1, v___x_582_);
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_784_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_585_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_587_);
v___x_792_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__39));
v___x_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_572_);
v___x_795_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkSharedFlags_568_);
v___x_796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_785_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*1, v___x_582_);
v___x_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_794_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___x_585_);
v___x_800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_587_);
v___x_801_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__41));
v___x_802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_572_);
v___x_804_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccFlags_569_);
v___x_805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_574_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*1, v___x_582_);
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_803_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_585_);
v___x_809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_587_);
v___x_810_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__43));
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___x_572_);
v___x_813_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__44, &l_Lake_instReprLeanInstall_repr___redArg___closed__44_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44);
v___x_814_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkStaticFlags_570_);
v___x_815_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_582_);
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_812_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_585_);
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v___x_587_);
v___x_820_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__46));
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_572_);
v___x_823_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkSharedFlags_571_);
v___x_824_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_813_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*1, v___x_582_);
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_822_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_828_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_826_);
v___x_830_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_827_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*1, v___x_582_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_834_, lean_object* v_prec_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_837_, lean_object* v_prec_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_instReprLeanInstall_repr(v_x_837_, v_prec_838_);
lean_dec(v_prec_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_System_Platform_isWindows;
if (v___x_843_ == 0)
{
lean_object* v_leanLibDir_844_; lean_object* v_systemLibDir_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_leanLibDir_844_ = lean_ctor_get(v_self_842_, 3);
v_systemLibDir_845_ = lean_ctor_get(v_self_842_, 5);
v___x_846_ = lean_box(0);
lean_inc_ref(v_systemLibDir_845_);
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v_systemLibDir_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
lean_inc_ref(v_leanLibDir_844_);
v___x_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_848_, 0, v_leanLibDir_844_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
return v___x_848_;
}
else
{
lean_object* v_binDir_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_binDir_849_ = lean_ctor_get(v_self_842_, 6);
v___x_850_ = lean_box(0);
lean_inc_ref(v_binDir_849_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v_binDir_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lake_LeanInstall_sharedLibPath(v_self_852_);
lean_dec_ref(v_self_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_854_){
_start:
{
uint8_t v_customCc_855_; 
v_customCc_855_ = lean_ctor_get_uint8(v_self_854_, sizeof(void*)*21);
if (v_customCc_855_ == 0)
{
lean_object* v___x_856_; 
v___x_856_ = lean_box(0);
return v___x_856_;
}
else
{
lean_object* v_cc_857_; lean_object* v___x_858_; 
v_cc_857_ = lean_ctor_get(v_self_854_, 14);
lean_inc_ref(v_cc_857_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_cc_857_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lake_LeanInstall_leanCc_x3f(v_self_859_);
lean_dec_ref(v_self_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_861_, lean_object* v_self_862_){
_start:
{
if (v_shared_861_ == 0)
{
lean_object* v_ccLinkStaticFlags_863_; 
v_ccLinkStaticFlags_863_ = lean_ctor_get(v_self_862_, 19);
lean_inc_ref(v_ccLinkStaticFlags_863_);
return v_ccLinkStaticFlags_863_;
}
else
{
lean_object* v_ccLinkSharedFlags_864_; 
v_ccLinkSharedFlags_864_ = lean_ctor_get(v_self_862_, 20);
lean_inc_ref(v_ccLinkSharedFlags_864_);
return v_ccLinkSharedFlags_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_865_, lean_object* v_self_866_){
_start:
{
uint8_t v_shared_boxed_867_; lean_object* v_res_868_; 
v_shared_boxed_867_ = lean_unbox(v_shared_865_);
v_res_868_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_867_, v_self_866_);
lean_dec_ref(v_self_866_);
return v_res_868_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = l_System_FilePath_exeExtension;
v___x_871_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_872_ = l_System_FilePath_addExtension(v___x_871_, v___x_870_);
return v___x_872_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_873_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = l_Lake_defaultBuildDir;
v___x_875_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_876_ = l_System_FilePath_join(v___x_875_, v___x_874_);
return v___x_876_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__1(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = l_Lake_defaultBinDir;
v___x_878_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_879_ = l_System_FilePath_join(v___x_878_, v___x_877_);
return v___x_879_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__2(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = l_Lake_defaultLeanLibDir;
v___x_881_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_882_ = l_System_FilePath_join(v___x_881_, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__4(void){
_start:
{
uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = 0;
v___x_885_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_886_ = l_Lake_nameToSharedLib(v___x_885_, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__5(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
v___x_888_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_889_ = l_System_FilePath_join(v___x_888_, v___x_887_);
return v___x_889_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__7(void){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_892_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__6));
v___x_893_ = 0;
v___x_894_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_895_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__5, &l_Lake_instInhabitedLakeInstall_default___closed__5_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__5);
v___x_896_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
lean_ctor_set(v___x_896_, 2, v___x_892_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*3, v___x_893_);
return v___x_896_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__8(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = l_Lake_lakeExe;
v___x_898_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_899_ = l_System_FilePath_join(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__9(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_900_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__8, &l_Lake_instInhabitedLakeInstall_default___closed__8_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__8);
v___x_901_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__7, &l_Lake_instInhabitedLakeInstall_default___closed__7_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__7);
v___x_902_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_903_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_904_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_905_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
lean_ctor_set(v___x_905_, 2, v___x_903_);
lean_ctor_set(v___x_905_, 3, v___x_902_);
lean_ctor_set(v___x_905_, 4, v___x_901_);
lean_ctor_set(v___x_905_, 5, v___x_900_);
return v___x_905_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__9, &l_Lake_instInhabitedLakeInstall_default___closed__9_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__9);
return v___x_906_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_916_){
_start:
{
lean_object* v_home_917_; lean_object* v_srcDir_918_; lean_object* v_binDir_919_; lean_object* v_libDir_920_; lean_object* v_sharedDynlib_921_; lean_object* v_lake_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_home_917_ = lean_ctor_get(v_x_916_, 0);
lean_inc_ref(v_home_917_);
v_srcDir_918_ = lean_ctor_get(v_x_916_, 1);
lean_inc_ref(v_srcDir_918_);
v_binDir_919_ = lean_ctor_get(v_x_916_, 2);
lean_inc_ref(v_binDir_919_);
v_libDir_920_ = lean_ctor_get(v_x_916_, 3);
lean_inc_ref(v_libDir_920_);
v_sharedDynlib_921_ = lean_ctor_get(v_x_916_, 4);
lean_inc_ref(v_sharedDynlib_921_);
v_lake_922_ = lean_ctor_get(v_x_916_, 5);
lean_inc_ref(v_lake_922_);
lean_dec_ref(v_x_916_);
v___x_923_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_924_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_925_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_928_ = l_String_quote(v_home_917_);
v___x_929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Repr_addAppParen(v___x_930_, v___x_926_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_925_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = 0;
v___x_934_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*1, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_924_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_box(1);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_923_);
v___x_943_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_944_ = l_String_quote(v_srcDir_918_);
v___x_945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_927_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Repr_addAppParen(v___x_946_, v___x_926_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_943_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_933_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_942_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_936_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_938_);
v___x_953_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_923_);
v___x_956_ = l_String_quote(v_binDir_919_);
v___x_957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_927_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l_Repr_addAppParen(v___x_958_, v___x_926_);
v___x_960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_943_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_933_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_955_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_936_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_938_);
v___x_965_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_923_);
v___x_968_ = l_String_quote(v_libDir_920_);
v___x_969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_927_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Repr_addAppParen(v___x_970_, v___x_926_);
v___x_972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_943_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_933_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_967_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_936_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_938_);
v___x_977_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__3));
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_923_);
v___x_980_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_981_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_921_);
v___x_982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_933_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_936_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_938_);
v___x_987_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__4));
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_923_);
v___x_990_ = l_String_quote(v_lake_922_);
v___x_991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_927_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Repr_addAppParen(v___x_992_, v___x_926_);
v___x_994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_925_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_933_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_989_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_998_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_996_);
v___x_1000_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*1, v___x_933_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_1004_, lean_object* v_prec_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_1007_, lean_object* v_prec_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lake_instReprLakeInstall_repr(v_x_1007_, v_prec_1008_);
lean_dec(v_prec_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_1012_){
_start:
{
lean_object* v_sharedDynlib_1013_; lean_object* v_path_1014_; 
v_sharedDynlib_1013_ = lean_ctor_get(v_self_1012_, 4);
v_path_1014_ = lean_ctor_get(v_sharedDynlib_1013_, 0);
lean_inc_ref(v_path_1014_);
return v_path_1014_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lake_LakeInstall_sharedLib(v_self_1015_);
lean_dec_ref(v_self_1015_);
return v_res_1016_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__2(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_lib_1021_; 
v___x_1019_ = l_Lake_sharedLibExt;
v___x_1020_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v_lib_1021_ = lean_string_append(v___x_1020_, v___x_1019_);
return v_lib_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_1022_){
_start:
{
lean_object* v_sysroot_1023_; lean_object* v_srcDir_1024_; lean_object* v_leanLibDir_1025_; lean_object* v_binDir_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___y_1030_; lean_object* v_lib_1038_; uint8_t v___x_1039_; 
v_sysroot_1023_ = lean_ctor_get(v_lean_1022_, 0);
lean_inc_ref(v_sysroot_1023_);
v_srcDir_1024_ = lean_ctor_get(v_lean_1022_, 2);
lean_inc_ref(v_srcDir_1024_);
v_leanLibDir_1025_ = lean_ctor_get(v_lean_1022_, 3);
lean_inc_ref(v_leanLibDir_1025_);
v_binDir_1026_ = lean_ctor_get(v_lean_1022_, 6);
lean_inc_ref(v_binDir_1026_);
lean_dec_ref(v_lean_1022_);
v___x_1027_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1028_ = l_System_FilePath_join(v_srcDir_1024_, v___x_1027_);
v_lib_1038_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__2, &l_Lake_LakeInstall_ofLean___closed__2_once, _init_l_Lake_LakeInstall_ofLean___closed__2);
v___x_1039_ = l_System_Platform_isWindows;
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_inc_ref(v_leanLibDir_1025_);
v___x_1040_ = l_System_FilePath_join(v_leanLibDir_1025_, v_lib_1038_);
v___y_1030_ = v___x_1040_;
goto v___jp_1029_;
}
else
{
lean_object* v___x_1041_; 
lean_inc_ref(v_binDir_1026_);
v___x_1041_ = l_System_FilePath_join(v_binDir_1026_, v_lib_1038_);
v___y_1030_ = v___x_1041_;
goto v___jp_1029_;
}
v___jp_1029_:
{
lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1031_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_1032_ = 0;
v___x_1033_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__6));
v___x_1034_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1034_, 0, v___y_1030_);
lean_ctor_set(v___x_1034_, 1, v___x_1031_);
lean_ctor_set(v___x_1034_, 2, v___x_1033_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*3, v___x_1032_);
v___x_1035_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_1026_);
v___x_1036_ = l_System_FilePath_join(v_binDir_1026_, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1037_, 0, v_sysroot_1023_);
lean_ctor_set(v___x_1037_, 1, v___x_1028_);
lean_ctor_set(v___x_1037_, 2, v_binDir_1026_);
lean_ctor_set(v___x_1037_, 3, v_leanLibDir_1025_);
lean_ctor_set(v___x_1037_, 4, v___x_1034_);
lean_ctor_set(v___x_1037_, 5, v___x_1036_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_1046_ = lean_io_getenv(v___x_1045_);
if (lean_obj_tag(v___x_1046_) == 1)
{
lean_object* v_val_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1074_; 
v_val_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1074_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_val_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1074_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___y_1054_; 
v___x_1051_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_1052_ = lean_io_getenv(v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_1054_ = v___x_1072_;
goto v___jp_1053_;
}
else
{
lean_object* v_val_1073_; 
v_val_1073_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1073_);
lean_dec_ref(v___x_1052_);
v___y_1054_ = v_val_1073_;
goto v___jp_1053_;
}
v___jp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_startInclusive_1059_; lean_object* v_endExclusive_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_string_utf8_byte_size(v___y_1054_);
lean_inc_ref(v___y_1054_);
v___x_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1057_, 0, v___y_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
v___x_1058_ = l_String_Slice_trimAscii(v___x_1057_);
v_startInclusive_1059_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_startInclusive_1059_);
v_endExclusive_1060_ = lean_ctor_get(v___x_1058_, 2);
lean_inc(v_endExclusive_1060_);
lean_dec_ref(v___x_1058_);
v___x_1061_ = lean_nat_sub(v_endExclusive_1060_, v_startInclusive_1059_);
lean_dec(v_startInclusive_1059_);
lean_dec(v_endExclusive_1060_);
v___x_1062_ = lean_nat_dec_eq(v___x_1061_, v___x_1055_);
lean_dec(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1063_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
lean_inc_n(v_val_1047_, 2);
v___x_1064_ = l_System_FilePath_join(v_val_1047_, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_1066_ = l_System_FilePath_join(v_val_1047_, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1067_, 0, v_val_1047_);
lean_ctor_set(v___x_1067_, 1, v___y_1054_);
lean_ctor_set(v___x_1067_, 2, v___x_1064_);
lean_ctor_set(v___x_1067_, 3, v___x_1066_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1067_);
v___x_1069_ = v___x_1049_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v___y_1054_);
lean_del_object(v___x_1049_);
lean_dec(v_val_1047_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
}
}
}
else
{
lean_object* v___x_1075_; 
lean_dec(v___x_1046_);
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lake_findElanInstall_x3f();
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1089_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1090_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1094_ = 1;
v___x_1095_ = 0;
v___x_1096_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1096_, 0, v___x_1089_);
lean_ctor_set(v___x_1096_, 1, v_lean_1087_);
lean_ctor_set(v___x_1096_, 2, v___x_1090_);
lean_ctor_set(v___x_1096_, 3, v___x_1091_);
lean_ctor_set(v___x_1096_, 4, v___x_1093_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*5, v___x_1094_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*5 + 1, v___x_1095_);
v___x_1097_ = l_IO_Process_output(v___x_1096_, v___x_1091_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1116_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1116_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1116_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
uint32_t v_exitCode_1102_; lean_object* v_stdout_1103_; uint32_t v___x_1104_; uint8_t v___x_1105_; 
v_exitCode_1102_ = lean_ctor_get_uint32(v_a_1098_, sizeof(void*)*2);
v_stdout_1103_ = lean_ctor_get(v_a_1098_, 0);
lean_inc_ref(v_stdout_1103_);
lean_dec(v_a_1098_);
v___x_1104_ = 0;
v___x_1105_ = lean_uint32_dec_eq(v_exitCode_1102_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v_stdout_1103_);
lean_del_object(v___x_1100_);
return v___x_1091_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_str_1109_; lean_object* v_startInclusive_1110_; lean_object* v_endExclusive_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1106_ = lean_string_utf8_byte_size(v_stdout_1103_);
v___x_1107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1107_, 0, v_stdout_1103_);
lean_ctor_set(v___x_1107_, 1, v___x_1092_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
v___x_1108_ = l_String_Slice_trimAscii(v___x_1107_);
v_str_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_str_1109_);
v_startInclusive_1110_ = lean_ctor_get(v___x_1108_, 1);
lean_inc(v_startInclusive_1110_);
v_endExclusive_1111_ = lean_ctor_get(v___x_1108_, 2);
lean_inc(v_endExclusive_1111_);
lean_dec_ref(v___x_1108_);
v___x_1112_ = lean_string_utf8_extract(v_str_1109_, v_startInclusive_1110_, v_endExclusive_1111_);
lean_dec(v_endExclusive_1111_);
lean_dec(v_startInclusive_1110_);
lean_dec_ref(v_str_1109_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1112_);
v___x_1114_ = v___x_1100_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_dec_ref(v___x_1097_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lake_findLeanSysroot_x3f(v_lean_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1127_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1128_ = l_Lake_leanExe(v_sysroot_1125_);
v___x_1129_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1133_ = 1;
v___x_1134_ = 0;
v___x_1135_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1135_, 0, v___x_1127_);
lean_ctor_set(v___x_1135_, 1, v___x_1128_);
lean_ctor_set(v___x_1135_, 2, v___x_1129_);
lean_ctor_set(v___x_1135_, 3, v___x_1130_);
lean_ctor_set(v___x_1135_, 4, v___x_1132_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*5, v___x_1133_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*5 + 1, v___x_1134_);
v___x_1136_ = l_IO_Process_output(v___x_1135_, v___x_1130_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_stdout_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_str_1142_; lean_object* v_startInclusive_1143_; lean_object* v_endExclusive_1144_; lean_object* v___x_1145_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v_stdout_1138_ = lean_ctor_get(v_a_1137_, 0);
lean_inc_ref(v_stdout_1138_);
lean_dec(v_a_1137_);
v___x_1139_ = lean_string_utf8_byte_size(v_stdout_1138_);
v___x_1140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1140_, 0, v_stdout_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1131_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
v___x_1141_ = l_String_Slice_trimAscii(v___x_1140_);
v_str_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_str_1142_);
v_startInclusive_1143_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_startInclusive_1143_);
v_endExclusive_1144_ = lean_ctor_get(v___x_1141_, 2);
lean_inc(v_endExclusive_1144_);
lean_dec_ref(v___x_1141_);
v___x_1145_ = lean_string_utf8_extract(v_str_1142_, v_startInclusive_1143_, v_endExclusive_1144_);
lean_dec(v_endExclusive_1144_);
lean_dec(v_startInclusive_1143_);
lean_dec_ref(v_str_1142_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
lean_dec_ref(v___x_1136_);
v___x_1146_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1155_ = lean_io_getenv(v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 1)
{
lean_object* v_val_1156_; 
lean_dec_ref(v_sysroot_1152_);
v_val_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_val_1156_);
lean_dec_ref(v___x_1155_);
return v_val_1156_;
}
else
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
lean_dec(v___x_1155_);
v___x_1157_ = l_Lake_leanArExe(v_sysroot_1152_);
v___x_1158_ = l_System_FilePath_pathExists(v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v___x_1157_);
v___x_1159_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1160_ = lean_io_getenv(v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 1)
{
lean_object* v_val_1161_; 
v_val_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_val_1161_);
lean_dec_ref(v___x_1160_);
return v_val_1161_;
}
else
{
lean_object* v___x_1162_; 
lean_dec(v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
return v___x_1162_;
}
}
else
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1166_, lean_object* v_i_1167_, lean_object* v_cc_1168_){
_start:
{
lean_object* v_sysroot_1169_; lean_object* v_githash_1170_; lean_object* v_srcDir_1171_; lean_object* v_leanLibDir_1172_; lean_object* v_includeDir_1173_; lean_object* v_systemLibDir_1174_; lean_object* v_binDir_1175_; lean_object* v_lean_1176_; lean_object* v_leanir_1177_; lean_object* v_leanc_1178_; lean_object* v_leantar_1179_; lean_object* v_sharedLib_1180_; lean_object* v_initSharedLib_1181_; lean_object* v_ar_1182_; lean_object* v_cFlags_1183_; lean_object* v_linkStaticFlags_1184_; lean_object* v_linkSharedFlags_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1198_; 
v_sysroot_1169_ = lean_ctor_get(v_i_1167_, 0);
v_githash_1170_ = lean_ctor_get(v_i_1167_, 1);
v_srcDir_1171_ = lean_ctor_get(v_i_1167_, 2);
v_leanLibDir_1172_ = lean_ctor_get(v_i_1167_, 3);
v_includeDir_1173_ = lean_ctor_get(v_i_1167_, 4);
v_systemLibDir_1174_ = lean_ctor_get(v_i_1167_, 5);
v_binDir_1175_ = lean_ctor_get(v_i_1167_, 6);
v_lean_1176_ = lean_ctor_get(v_i_1167_, 7);
v_leanir_1177_ = lean_ctor_get(v_i_1167_, 8);
v_leanc_1178_ = lean_ctor_get(v_i_1167_, 9);
v_leantar_1179_ = lean_ctor_get(v_i_1167_, 10);
v_sharedLib_1180_ = lean_ctor_get(v_i_1167_, 11);
v_initSharedLib_1181_ = lean_ctor_get(v_i_1167_, 12);
v_ar_1182_ = lean_ctor_get(v_i_1167_, 13);
v_cFlags_1183_ = lean_ctor_get(v_i_1167_, 15);
v_linkStaticFlags_1184_ = lean_ctor_get(v_i_1167_, 16);
v_linkSharedFlags_1185_ = lean_ctor_get(v_i_1167_, 17);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_i_1167_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; lean_object* v_unused_1201_; lean_object* v_unused_1202_; 
v_unused_1199_ = lean_ctor_get(v_i_1167_, 20);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_i_1167_, 19);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_i_1167_, 18);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_i_1167_, 14);
lean_dec(v_unused_1202_);
v___x_1187_ = v_i_1167_;
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_linkSharedFlags_1185_);
lean_inc(v_linkStaticFlags_1184_);
lean_inc(v_cFlags_1183_);
lean_inc(v_ar_1182_);
lean_inc(v_initSharedLib_1181_);
lean_inc(v_sharedLib_1180_);
lean_inc(v_leantar_1179_);
lean_inc(v_leanc_1178_);
lean_inc(v_leanir_1177_);
lean_inc(v_lean_1176_);
lean_inc(v_binDir_1175_);
lean_inc(v_systemLibDir_1174_);
lean_inc(v_includeDir_1173_);
lean_inc(v_leanLibDir_1172_);
lean_inc(v_srcDir_1171_);
lean_inc(v_githash_1170_);
lean_inc(v_sysroot_1169_);
lean_dec(v_i_1167_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_ccLinkFlags_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v_ccLinkFlags_1189_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1166_);
v___x_1190_ = 0;
v___x_1191_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1166_);
lean_inc_ref(v_cFlags_1183_);
v___x_1192_ = l_Array_append___redArg(v_cFlags_1183_, v___x_1191_);
lean_dec_ref(v___x_1191_);
lean_inc_ref(v_ccLinkFlags_1189_);
v___x_1193_ = l_Array_append___redArg(v_ccLinkFlags_1189_, v_linkStaticFlags_1184_);
v___x_1194_ = l_Array_append___redArg(v_ccLinkFlags_1189_, v_linkSharedFlags_1185_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 20, v___x_1194_);
lean_ctor_set(v___x_1187_, 19, v___x_1193_);
lean_ctor_set(v___x_1187_, 18, v___x_1192_);
lean_ctor_set(v___x_1187_, 14, v_cc_1168_);
v___x_1196_ = v___x_1187_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_sysroot_1169_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_githash_1170_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_srcDir_1171_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_leanLibDir_1172_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_includeDir_1173_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v_systemLibDir_1174_);
lean_ctor_set(v_reuseFailAlloc_1197_, 6, v_binDir_1175_);
lean_ctor_set(v_reuseFailAlloc_1197_, 7, v_lean_1176_);
lean_ctor_set(v_reuseFailAlloc_1197_, 8, v_leanir_1177_);
lean_ctor_set(v_reuseFailAlloc_1197_, 9, v_leanc_1178_);
lean_ctor_set(v_reuseFailAlloc_1197_, 10, v_leantar_1179_);
lean_ctor_set(v_reuseFailAlloc_1197_, 11, v_sharedLib_1180_);
lean_ctor_set(v_reuseFailAlloc_1197_, 12, v_initSharedLib_1181_);
lean_ctor_set(v_reuseFailAlloc_1197_, 13, v_ar_1182_);
lean_ctor_set(v_reuseFailAlloc_1197_, 14, v_cc_1168_);
lean_ctor_set(v_reuseFailAlloc_1197_, 15, v_cFlags_1183_);
lean_ctor_set(v_reuseFailAlloc_1197_, 16, v_linkStaticFlags_1184_);
lean_ctor_set(v_reuseFailAlloc_1197_, 17, v_linkSharedFlags_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 18, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1197_, 19, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1197_, 20, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*21, v___x_1190_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1203_, lean_object* v_i_1204_, lean_object* v_cc_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1203_, v_i_1204_, v_cc_1205_);
lean_dec_ref(v_sysroot_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1207_, lean_object* v_cc_1208_){
_start:
{
lean_object* v_sysroot_1209_; lean_object* v_githash_1210_; lean_object* v_srcDir_1211_; lean_object* v_leanLibDir_1212_; lean_object* v_includeDir_1213_; lean_object* v_systemLibDir_1214_; lean_object* v_binDir_1215_; lean_object* v_lean_1216_; lean_object* v_leanir_1217_; lean_object* v_leanc_1218_; lean_object* v_leantar_1219_; lean_object* v_sharedLib_1220_; lean_object* v_initSharedLib_1221_; lean_object* v_ar_1222_; uint8_t v_customCc_1223_; lean_object* v_cFlags_1224_; lean_object* v_linkStaticFlags_1225_; lean_object* v_linkSharedFlags_1226_; lean_object* v_ccFlags_1227_; lean_object* v_ccLinkStaticFlags_1228_; lean_object* v_ccLinkSharedFlags_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_sysroot_1209_ = lean_ctor_get(v_i_1207_, 0);
v_githash_1210_ = lean_ctor_get(v_i_1207_, 1);
v_srcDir_1211_ = lean_ctor_get(v_i_1207_, 2);
v_leanLibDir_1212_ = lean_ctor_get(v_i_1207_, 3);
v_includeDir_1213_ = lean_ctor_get(v_i_1207_, 4);
v_systemLibDir_1214_ = lean_ctor_get(v_i_1207_, 5);
v_binDir_1215_ = lean_ctor_get(v_i_1207_, 6);
v_lean_1216_ = lean_ctor_get(v_i_1207_, 7);
v_leanir_1217_ = lean_ctor_get(v_i_1207_, 8);
v_leanc_1218_ = lean_ctor_get(v_i_1207_, 9);
v_leantar_1219_ = lean_ctor_get(v_i_1207_, 10);
v_sharedLib_1220_ = lean_ctor_get(v_i_1207_, 11);
v_initSharedLib_1221_ = lean_ctor_get(v_i_1207_, 12);
v_ar_1222_ = lean_ctor_get(v_i_1207_, 13);
v_customCc_1223_ = lean_ctor_get_uint8(v_i_1207_, sizeof(void*)*21);
v_cFlags_1224_ = lean_ctor_get(v_i_1207_, 15);
v_linkStaticFlags_1225_ = lean_ctor_get(v_i_1207_, 16);
v_linkSharedFlags_1226_ = lean_ctor_get(v_i_1207_, 17);
v_ccFlags_1227_ = lean_ctor_get(v_i_1207_, 18);
v_ccLinkStaticFlags_1228_ = lean_ctor_get(v_i_1207_, 19);
v_ccLinkSharedFlags_1229_ = lean_ctor_get(v_i_1207_, 20);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_i_1207_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_i_1207_, 14);
lean_dec(v_unused_1237_);
v___x_1231_ = v_i_1207_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1229_);
lean_inc(v_ccLinkStaticFlags_1228_);
lean_inc(v_ccFlags_1227_);
lean_inc(v_linkSharedFlags_1226_);
lean_inc(v_linkStaticFlags_1225_);
lean_inc(v_cFlags_1224_);
lean_inc(v_ar_1222_);
lean_inc(v_initSharedLib_1221_);
lean_inc(v_sharedLib_1220_);
lean_inc(v_leantar_1219_);
lean_inc(v_leanc_1218_);
lean_inc(v_leanir_1217_);
lean_inc(v_lean_1216_);
lean_inc(v_binDir_1215_);
lean_inc(v_systemLibDir_1214_);
lean_inc(v_includeDir_1213_);
lean_inc(v_leanLibDir_1212_);
lean_inc(v_srcDir_1211_);
lean_inc(v_githash_1210_);
lean_inc(v_sysroot_1209_);
lean_dec(v_i_1207_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 14, v_cc_1208_);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_sysroot_1209_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_githash_1210_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_srcDir_1211_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_leanLibDir_1212_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_includeDir_1213_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v_systemLibDir_1214_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_binDir_1215_);
lean_ctor_set(v_reuseFailAlloc_1235_, 7, v_lean_1216_);
lean_ctor_set(v_reuseFailAlloc_1235_, 8, v_leanir_1217_);
lean_ctor_set(v_reuseFailAlloc_1235_, 9, v_leanc_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 10, v_leantar_1219_);
lean_ctor_set(v_reuseFailAlloc_1235_, 11, v_sharedLib_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 12, v_initSharedLib_1221_);
lean_ctor_set(v_reuseFailAlloc_1235_, 13, v_ar_1222_);
lean_ctor_set(v_reuseFailAlloc_1235_, 14, v_cc_1208_);
lean_ctor_set(v_reuseFailAlloc_1235_, 15, v_cFlags_1224_);
lean_ctor_set(v_reuseFailAlloc_1235_, 16, v_linkStaticFlags_1225_);
lean_ctor_set(v_reuseFailAlloc_1235_, 17, v_linkSharedFlags_1226_);
lean_ctor_set(v_reuseFailAlloc_1235_, 18, v_ccFlags_1227_);
lean_ctor_set(v_reuseFailAlloc_1235_, 19, v_ccLinkStaticFlags_1228_);
lean_ctor_set(v_reuseFailAlloc_1235_, 20, v_ccLinkSharedFlags_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*21, v_customCc_1223_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1240_, lean_object* v_i_1241_){
_start:
{
lean_object* v_cc_1244_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1275_ = lean_io_getenv(v___x_1274_);
if (lean_obj_tag(v___x_1275_) == 1)
{
lean_object* v_val_1276_; 
lean_dec_ref(v_sysroot_1240_);
v_val_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1276_);
lean_dec_ref(v___x_1275_);
v_cc_1244_ = v_val_1276_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
lean_dec(v___x_1275_);
lean_inc_ref(v_sysroot_1240_);
v___x_1277_ = l_Lake_leanCcExe(v_sysroot_1240_);
v___x_1278_ = l_System_FilePath_pathExists(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_sysroot_1240_);
v___x_1279_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1280_ = lean_io_getenv(v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref(v___x_1280_);
v_cc_1244_ = v_val_1281_;
goto v___jp_1243_;
}
else
{
lean_object* v_sysroot_1282_; lean_object* v_githash_1283_; lean_object* v_srcDir_1284_; lean_object* v_leanLibDir_1285_; lean_object* v_includeDir_1286_; lean_object* v_systemLibDir_1287_; lean_object* v_binDir_1288_; lean_object* v_lean_1289_; lean_object* v_leanir_1290_; lean_object* v_leanc_1291_; lean_object* v_leantar_1292_; lean_object* v_sharedLib_1293_; lean_object* v_initSharedLib_1294_; lean_object* v_ar_1295_; uint8_t v_customCc_1296_; lean_object* v_cFlags_1297_; lean_object* v_linkStaticFlags_1298_; lean_object* v_linkSharedFlags_1299_; lean_object* v_ccFlags_1300_; lean_object* v_ccLinkStaticFlags_1301_; lean_object* v_ccLinkSharedFlags_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___x_1280_);
v_sysroot_1282_ = lean_ctor_get(v_i_1241_, 0);
v_githash_1283_ = lean_ctor_get(v_i_1241_, 1);
v_srcDir_1284_ = lean_ctor_get(v_i_1241_, 2);
v_leanLibDir_1285_ = lean_ctor_get(v_i_1241_, 3);
v_includeDir_1286_ = lean_ctor_get(v_i_1241_, 4);
v_systemLibDir_1287_ = lean_ctor_get(v_i_1241_, 5);
v_binDir_1288_ = lean_ctor_get(v_i_1241_, 6);
v_lean_1289_ = lean_ctor_get(v_i_1241_, 7);
v_leanir_1290_ = lean_ctor_get(v_i_1241_, 8);
v_leanc_1291_ = lean_ctor_get(v_i_1241_, 9);
v_leantar_1292_ = lean_ctor_get(v_i_1241_, 10);
v_sharedLib_1293_ = lean_ctor_get(v_i_1241_, 11);
v_initSharedLib_1294_ = lean_ctor_get(v_i_1241_, 12);
v_ar_1295_ = lean_ctor_get(v_i_1241_, 13);
v_customCc_1296_ = lean_ctor_get_uint8(v_i_1241_, sizeof(void*)*21);
v_cFlags_1297_ = lean_ctor_get(v_i_1241_, 15);
v_linkStaticFlags_1298_ = lean_ctor_get(v_i_1241_, 16);
v_linkSharedFlags_1299_ = lean_ctor_get(v_i_1241_, 17);
v_ccFlags_1300_ = lean_ctor_get(v_i_1241_, 18);
v_ccLinkStaticFlags_1301_ = lean_ctor_get(v_i_1241_, 19);
v_ccLinkSharedFlags_1302_ = lean_ctor_get(v_i_1241_, 20);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_i_1241_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v_i_1241_, 14);
lean_dec(v_unused_1311_);
v___x_1304_ = v_i_1241_;
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1302_);
lean_inc(v_ccLinkStaticFlags_1301_);
lean_inc(v_ccFlags_1300_);
lean_inc(v_linkSharedFlags_1299_);
lean_inc(v_linkStaticFlags_1298_);
lean_inc(v_cFlags_1297_);
lean_inc(v_ar_1295_);
lean_inc(v_initSharedLib_1294_);
lean_inc(v_sharedLib_1293_);
lean_inc(v_leantar_1292_);
lean_inc(v_leanc_1291_);
lean_inc(v_leanir_1290_);
lean_inc(v_lean_1289_);
lean_inc(v_binDir_1288_);
lean_inc(v_systemLibDir_1287_);
lean_inc(v_includeDir_1286_);
lean_inc(v_leanLibDir_1285_);
lean_inc(v_srcDir_1284_);
lean_inc(v_githash_1283_);
lean_inc(v_sysroot_1282_);
lean_dec(v_i_1241_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 14, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_sysroot_1282_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_githash_1283_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_srcDir_1284_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_leanLibDir_1285_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_includeDir_1286_);
lean_ctor_set(v_reuseFailAlloc_1309_, 5, v_systemLibDir_1287_);
lean_ctor_set(v_reuseFailAlloc_1309_, 6, v_binDir_1288_);
lean_ctor_set(v_reuseFailAlloc_1309_, 7, v_lean_1289_);
lean_ctor_set(v_reuseFailAlloc_1309_, 8, v_leanir_1290_);
lean_ctor_set(v_reuseFailAlloc_1309_, 9, v_leanc_1291_);
lean_ctor_set(v_reuseFailAlloc_1309_, 10, v_leantar_1292_);
lean_ctor_set(v_reuseFailAlloc_1309_, 11, v_sharedLib_1293_);
lean_ctor_set(v_reuseFailAlloc_1309_, 12, v_initSharedLib_1294_);
lean_ctor_set(v_reuseFailAlloc_1309_, 13, v_ar_1295_);
lean_ctor_set(v_reuseFailAlloc_1309_, 14, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1309_, 15, v_cFlags_1297_);
lean_ctor_set(v_reuseFailAlloc_1309_, 16, v_linkStaticFlags_1298_);
lean_ctor_set(v_reuseFailAlloc_1309_, 17, v_linkSharedFlags_1299_);
lean_ctor_set(v_reuseFailAlloc_1309_, 18, v_ccFlags_1300_);
lean_ctor_set(v_reuseFailAlloc_1309_, 19, v_ccLinkStaticFlags_1301_);
lean_ctor_set(v_reuseFailAlloc_1309_, 20, v_ccLinkSharedFlags_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*21, v_customCc_1296_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1240_, v_i_1241_, v___x_1277_);
lean_dec_ref(v_sysroot_1240_);
return v___x_1312_;
}
}
v___jp_1243_:
{
lean_object* v_sysroot_1245_; lean_object* v_githash_1246_; lean_object* v_srcDir_1247_; lean_object* v_leanLibDir_1248_; lean_object* v_includeDir_1249_; lean_object* v_systemLibDir_1250_; lean_object* v_binDir_1251_; lean_object* v_lean_1252_; lean_object* v_leanir_1253_; lean_object* v_leanc_1254_; lean_object* v_leantar_1255_; lean_object* v_sharedLib_1256_; lean_object* v_initSharedLib_1257_; lean_object* v_ar_1258_; uint8_t v_customCc_1259_; lean_object* v_cFlags_1260_; lean_object* v_linkStaticFlags_1261_; lean_object* v_linkSharedFlags_1262_; lean_object* v_ccFlags_1263_; lean_object* v_ccLinkStaticFlags_1264_; lean_object* v_ccLinkSharedFlags_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_sysroot_1245_ = lean_ctor_get(v_i_1241_, 0);
v_githash_1246_ = lean_ctor_get(v_i_1241_, 1);
v_srcDir_1247_ = lean_ctor_get(v_i_1241_, 2);
v_leanLibDir_1248_ = lean_ctor_get(v_i_1241_, 3);
v_includeDir_1249_ = lean_ctor_get(v_i_1241_, 4);
v_systemLibDir_1250_ = lean_ctor_get(v_i_1241_, 5);
v_binDir_1251_ = lean_ctor_get(v_i_1241_, 6);
v_lean_1252_ = lean_ctor_get(v_i_1241_, 7);
v_leanir_1253_ = lean_ctor_get(v_i_1241_, 8);
v_leanc_1254_ = lean_ctor_get(v_i_1241_, 9);
v_leantar_1255_ = lean_ctor_get(v_i_1241_, 10);
v_sharedLib_1256_ = lean_ctor_get(v_i_1241_, 11);
v_initSharedLib_1257_ = lean_ctor_get(v_i_1241_, 12);
v_ar_1258_ = lean_ctor_get(v_i_1241_, 13);
v_customCc_1259_ = lean_ctor_get_uint8(v_i_1241_, sizeof(void*)*21);
v_cFlags_1260_ = lean_ctor_get(v_i_1241_, 15);
v_linkStaticFlags_1261_ = lean_ctor_get(v_i_1241_, 16);
v_linkSharedFlags_1262_ = lean_ctor_get(v_i_1241_, 17);
v_ccFlags_1263_ = lean_ctor_get(v_i_1241_, 18);
v_ccLinkStaticFlags_1264_ = lean_ctor_get(v_i_1241_, 19);
v_ccLinkSharedFlags_1265_ = lean_ctor_get(v_i_1241_, 20);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_i_1241_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v_i_1241_, 14);
lean_dec(v_unused_1273_);
v___x_1267_ = v_i_1241_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1265_);
lean_inc(v_ccLinkStaticFlags_1264_);
lean_inc(v_ccFlags_1263_);
lean_inc(v_linkSharedFlags_1262_);
lean_inc(v_linkStaticFlags_1261_);
lean_inc(v_cFlags_1260_);
lean_inc(v_ar_1258_);
lean_inc(v_initSharedLib_1257_);
lean_inc(v_sharedLib_1256_);
lean_inc(v_leantar_1255_);
lean_inc(v_leanc_1254_);
lean_inc(v_leanir_1253_);
lean_inc(v_lean_1252_);
lean_inc(v_binDir_1251_);
lean_inc(v_systemLibDir_1250_);
lean_inc(v_includeDir_1249_);
lean_inc(v_leanLibDir_1248_);
lean_inc(v_srcDir_1247_);
lean_inc(v_githash_1246_);
lean_inc(v_sysroot_1245_);
lean_dec(v_i_1241_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 14, v_cc_1244_);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_sysroot_1245_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_githash_1246_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_srcDir_1247_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_leanLibDir_1248_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_includeDir_1249_);
lean_ctor_set(v_reuseFailAlloc_1271_, 5, v_systemLibDir_1250_);
lean_ctor_set(v_reuseFailAlloc_1271_, 6, v_binDir_1251_);
lean_ctor_set(v_reuseFailAlloc_1271_, 7, v_lean_1252_);
lean_ctor_set(v_reuseFailAlloc_1271_, 8, v_leanir_1253_);
lean_ctor_set(v_reuseFailAlloc_1271_, 9, v_leanc_1254_);
lean_ctor_set(v_reuseFailAlloc_1271_, 10, v_leantar_1255_);
lean_ctor_set(v_reuseFailAlloc_1271_, 11, v_sharedLib_1256_);
lean_ctor_set(v_reuseFailAlloc_1271_, 12, v_initSharedLib_1257_);
lean_ctor_set(v_reuseFailAlloc_1271_, 13, v_ar_1258_);
lean_ctor_set(v_reuseFailAlloc_1271_, 14, v_cc_1244_);
lean_ctor_set(v_reuseFailAlloc_1271_, 15, v_cFlags_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 16, v_linkStaticFlags_1261_);
lean_ctor_set(v_reuseFailAlloc_1271_, 17, v_linkSharedFlags_1262_);
lean_ctor_set(v_reuseFailAlloc_1271_, 18, v_ccFlags_1263_);
lean_ctor_set(v_reuseFailAlloc_1271_, 19, v_ccLinkStaticFlags_1264_);
lean_ctor_set(v_reuseFailAlloc_1271_, 20, v_ccLinkSharedFlags_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*21, v_customCc_1259_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1313_, lean_object* v_i_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1313_, v_i_1314_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1317_, uint8_t v_collocated_1318_){
_start:
{
lean_object* v_githash_1321_; 
if (v_collocated_1318_ == 0)
{
lean_object* v___x_1350_; 
lean_inc_ref(v_sysroot_1317_);
v___x_1350_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1317_);
v_githash_1321_ = v___x_1350_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_githash;
v_githash_1321_ = v___x_1351_;
goto v___jp_1320_;
}
v___jp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_inc_ref_n(v_sysroot_1317_, 11);
v___x_1322_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1317_);
v___x_1323_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1324_ = l_System_FilePath_join(v_sysroot_1317_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1326_ = l_System_FilePath_join(v___x_1324_, v___x_1325_);
v___x_1327_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1328_ = l_System_FilePath_join(v_sysroot_1317_, v___x_1327_);
lean_inc_ref(v___x_1328_);
v___x_1329_ = l_System_FilePath_join(v___x_1328_, v___x_1325_);
v___x_1330_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1331_ = l_System_FilePath_join(v_sysroot_1317_, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1333_ = l_System_FilePath_join(v_sysroot_1317_, v___x_1332_);
v___x_1334_ = l_Lake_leanExe(v_sysroot_1317_);
v___x_1335_ = l_Lake_leanirExe(v_sysroot_1317_);
v___x_1336_ = l_Lake_leancExe(v_sysroot_1317_);
v___x_1337_ = l_Lake_leantarExe(v_sysroot_1317_);
v___x_1338_ = l_Lake_leanSharedLibDir(v_sysroot_1317_);
v___x_1339_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1338_);
v___x_1340_ = l_System_FilePath_join(v___x_1338_, v___x_1339_);
v___x_1341_ = l_Lake_initSharedLib;
v___x_1342_ = l_System_FilePath_join(v___x_1338_, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_1344_ = 1;
v___x_1345_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1346_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_1347_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
v___x_1348_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1348_, 0, v_sysroot_1317_);
lean_ctor_set(v___x_1348_, 1, v_githash_1321_);
lean_ctor_set(v___x_1348_, 2, v___x_1326_);
lean_ctor_set(v___x_1348_, 3, v___x_1329_);
lean_ctor_set(v___x_1348_, 4, v___x_1331_);
lean_ctor_set(v___x_1348_, 5, v___x_1328_);
lean_ctor_set(v___x_1348_, 6, v___x_1333_);
lean_ctor_set(v___x_1348_, 7, v___x_1334_);
lean_ctor_set(v___x_1348_, 8, v___x_1335_);
lean_ctor_set(v___x_1348_, 9, v___x_1336_);
lean_ctor_set(v___x_1348_, 10, v___x_1337_);
lean_ctor_set(v___x_1348_, 11, v___x_1340_);
lean_ctor_set(v___x_1348_, 12, v___x_1342_);
lean_ctor_set(v___x_1348_, 13, v___x_1322_);
lean_ctor_set(v___x_1348_, 14, v___x_1343_);
lean_ctor_set(v___x_1348_, 15, v___x_1345_);
lean_ctor_set(v___x_1348_, 16, v___x_1346_);
lean_ctor_set(v___x_1348_, 17, v___x_1347_);
lean_ctor_set(v___x_1348_, 18, v___x_1345_);
lean_ctor_set(v___x_1348_, 19, v___x_1346_);
lean_ctor_set(v___x_1348_, 20, v___x_1347_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*21, v___x_1344_);
v___x_1349_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1317_, v___x_1348_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1352_, lean_object* v_collocated_1353_, lean_object* v_a_1354_){
_start:
{
uint8_t v_collocated_boxed_1355_; lean_object* v_res_1356_; 
v_collocated_boxed_1355_ = lean_unbox(v_collocated_1353_);
v_res_1356_ = l_Lake_LeanInstall_get(v_sysroot_1352_, v_collocated_boxed_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lake_findLeanSysroot_x3f(v_lean_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_box(0);
return v___x_1360_;
}
else
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v_val_1361_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1363_ = v___x_1359_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v___x_1359_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_io_app_path();
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = l_System_FilePath_parent(v_a_1378_);
if (lean_obj_tag(v___x_1379_) == 1)
{
lean_object* v_val_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_n(v_val_1380_, 2);
lean_dec_ref(v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1382_ = l_System_FilePath_join(v_val_1380_, v___x_1381_);
v___x_1383_ = l_System_FilePath_exeExtension;
v___x_1384_ = l_System_FilePath_addExtension(v___x_1382_, v___x_1383_);
v___x_1385_ = l_System_FilePath_pathExists(v___x_1384_);
lean_dec_ref(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec(v_val_1380_);
goto v___jp_1375_;
}
else
{
lean_object* v___x_1386_; 
v___x_1386_ = l_System_FilePath_parent(v_val_1380_);
return v___x_1386_;
}
}
else
{
lean_dec(v___x_1379_);
goto v___jp_1375_;
}
}
else
{
lean_dec_ref(v___x_1377_);
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_System_FilePath_parent(v_lake_1389_);
if (lean_obj_tag(v___x_1390_) == 0)
{
return v___x_1390_;
}
else
{
lean_object* v_val_1391_; lean_object* v___x_1392_; 
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = l_System_FilePath_parent(v_val_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
return v___x_1392_;
}
else
{
lean_object* v_val_1393_; lean_object* v___x_1394_; 
v_val_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1393_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = l_System_FilePath_parent(v_val_1393_);
if (lean_obj_tag(v___x_1394_) == 0)
{
return v___x_1394_;
}
else
{
lean_object* v_val_1395_; lean_object* v___x_1396_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = l_System_FilePath_parent(v_val_1395_);
return v___x_1396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1398_){
_start:
{
lean_object* v___x_1400_; 
lean_inc_ref(v_lake_1398_);
v___x_1400_ = l_Lake_lakeBuildHome_x3f(v_lake_1398_);
if (lean_obj_tag(v___x_1400_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_val_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_lake_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1405_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1401_, 2);
v___x_1406_ = l_System_FilePath_join(v_val_1401_, v___x_1405_);
v___x_1407_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1406_);
v___x_1408_ = l_System_FilePath_join(v___x_1406_, v___x_1407_);
v___x_1409_ = l_Lake_defaultLeanLibDir;
v___x_1410_ = l_System_FilePath_join(v___x_1406_, v___x_1409_);
v___x_1411_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1412_ = 0;
v___x_1413_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref_n(v___x_1410_, 2);
v___x_1414_ = l_System_FilePath_join(v___x_1410_, v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__6));
v___x_1416_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1411_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*3, v___x_1412_);
v_lake_1417_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1417_, 0, v_val_1401_);
lean_ctor_set(v_lake_1417_, 1, v_val_1401_);
lean_ctor_set(v_lake_1417_, 2, v___x_1408_);
lean_ctor_set(v_lake_1417_, 3, v___x_1410_);
lean_ctor_set(v_lake_1417_, 4, v___x_1416_);
lean_ctor_set(v_lake_1417_, 5, v_lake_1398_);
v___x_1418_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1419_ = l_System_FilePath_join(v___x_1410_, v___x_1418_);
v___x_1420_ = l_System_FilePath_pathExists(v___x_1419_);
lean_dec_ref(v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_lake_1417_);
lean_del_object(v___x_1403_);
v___x_1421_ = lean_box(0);
return v___x_1421_;
}
else
{
lean_object* v___x_1423_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_lake_1417_);
v___x_1423_ = v___x_1403_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_lake_1417_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v___x_1400_);
lean_dec_ref(v_lake_1398_);
v___x_1426_ = lean_box(0);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lake_getLakeInstall_x3f(v_lake_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1434_ = lean_io_getenv(v___x_1433_);
if (lean_obj_tag(v___x_1434_) == 1)
{
lean_object* v_val_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1444_; 
v_val_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1444_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_val_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1444_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1439_ = 0;
v___x_1440_ = l_Lake_LeanInstall_get(v_val_1435_, v___x_1439_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1440_);
v___x_1442_ = v___x_1437_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_lean_1448_; 
lean_dec(v___x_1434_);
v___x_1445_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1446_ = lean_io_getenv(v___x_1445_);
if (lean_obj_tag(v___x_1446_) == 1)
{
lean_object* v_val_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_startInclusive_1466_; lean_object* v_endExclusive_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_val_1461_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_n(v_val_1461_, 2);
lean_dec_ref(v___x_1446_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_string_utf8_byte_size(v_val_1461_);
v___x_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1464_, 0, v_val_1461_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = l_String_Slice_trimAscii(v___x_1464_);
v_startInclusive_1466_ = lean_ctor_get(v___x_1465_, 1);
lean_inc(v_startInclusive_1466_);
v_endExclusive_1467_ = lean_ctor_get(v___x_1465_, 2);
lean_inc(v_endExclusive_1467_);
lean_dec_ref(v___x_1465_);
v___x_1468_ = lean_nat_sub(v_endExclusive_1467_, v_startInclusive_1466_);
lean_dec(v_startInclusive_1466_);
lean_dec(v_endExclusive_1467_);
v___x_1469_ = lean_nat_dec_eq(v___x_1468_, v___x_1462_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
v_lean_1448_ = v_val_1461_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1470_; 
lean_dec(v_val_1461_);
v___x_1470_ = lean_box(0);
return v___x_1470_;
}
}
else
{
lean_object* v___x_1471_; 
lean_dec(v___x_1446_);
v___x_1471_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v_lean_1448_ = v___x_1471_;
goto v___jp_1447_;
}
v___jp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lake_findLeanSysroot_x3f(v_lean_1448_);
if (lean_obj_tag(v___x_1449_) == 1)
{
lean_object* v_val_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1459_; 
v_val_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_val_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1454_ = 0;
v___x_1455_ = l_Lake_LeanInstall_get(v_val_1450_, v___x_1454_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v___x_1449_);
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lake_findLeanInstall_x3f();
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_io_app_path();
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = l_Lake_getLakeInstall_x3f(v_a_1504_);
if (lean_obj_tag(v___x_1505_) == 1)
{
return v___x_1505_;
}
else
{
lean_dec(v___x_1505_);
goto v___jp_1476_;
}
}
else
{
lean_dec_ref(v___x_1503_);
goto v___jp_1476_;
}
v___jp_1476_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1478_ = lean_io_getenv(v___x_1477_);
if (lean_obj_tag(v___x_1478_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1501_; 
v_val_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1501_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1501_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1483_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1479_, 2);
v___x_1484_ = l_System_FilePath_join(v_val_1479_, v___x_1483_);
v___x_1485_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1484_);
v___x_1486_ = l_System_FilePath_join(v___x_1484_, v___x_1485_);
v___x_1487_ = l_Lake_defaultLeanLibDir;
v___x_1488_ = l_System_FilePath_join(v___x_1484_, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1490_ = 0;
v___x_1491_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref(v___x_1488_);
v___x_1492_ = l_System_FilePath_join(v___x_1488_, v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__6));
v___x_1494_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1489_);
lean_ctor_set(v___x_1494_, 2, v___x_1493_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*3, v___x_1490_);
v___x_1495_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1486_);
v___x_1496_ = l_System_FilePath_join(v___x_1486_, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1497_, 0, v_val_1479_);
lean_ctor_set(v___x_1497_, 1, v_val_1479_);
lean_ctor_set(v___x_1497_, 2, v___x_1486_);
lean_ctor_set(v___x_1497_, 3, v___x_1488_);
lean_ctor_set(v___x_1497_, 4, v___x_1494_);
lean_ctor_set(v___x_1497_, 5, v___x_1496_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1497_);
v___x_1499_ = v___x_1481_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v___x_1478_);
v___x_1502_ = lean_box(0);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lake_findLakeInstall_x3f();
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = l_Lake_findElanInstall_x3f();
v___x_1511_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1511_) == 1)
{
lean_object* v_val_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1572_; 
v_val_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1572_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_val_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1572_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1517_ = lean_io_getenv(v___x_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
goto v___jp_1518_;
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1529_; 
v_val_1528_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1517_);
v___x_1529_ = l_Lake_envToBool_x3f(v_val_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
goto v___jp_1518_;
}
else
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1571_; 
v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1571_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1571_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_unbox(v_val_1530_);
if (v___x_1534_ == 0)
{
lean_del_object(v___x_1532_);
lean_dec(v_val_1530_);
goto v___jp_1518_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_del_object(v___x_1514_);
v___x_1535_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1536_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
lean_inc_n(v_val_1512_, 9);
v___x_1537_ = l_System_FilePath_join(v_val_1512_, v___x_1536_);
v___x_1538_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1539_ = l_System_FilePath_join(v___x_1537_, v___x_1538_);
v___x_1540_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1541_ = l_System_FilePath_join(v_val_1512_, v___x_1540_);
lean_inc_ref(v___x_1541_);
v___x_1542_ = l_System_FilePath_join(v___x_1541_, v___x_1538_);
v___x_1543_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1544_ = l_System_FilePath_join(v_val_1512_, v___x_1543_);
v___x_1545_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1546_ = l_System_FilePath_join(v_val_1512_, v___x_1545_);
v___x_1547_ = l_Lake_leanExe(v_val_1512_);
v___x_1548_ = l_Lake_leanirExe(v_val_1512_);
v___x_1549_ = l_Lake_leancExe(v_val_1512_);
v___x_1550_ = l_Lake_leantarExe(v_val_1512_);
v___x_1551_ = l_Lake_leanSharedLibDir(v_val_1512_);
v___x_1552_ = l_Lake_leanSharedLib;
lean_inc_ref(v___x_1551_);
v___x_1553_ = l_System_FilePath_join(v___x_1551_, v___x_1552_);
v___x_1554_ = l_Lake_initSharedLib;
v___x_1555_ = l_System_FilePath_join(v___x_1551_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1557_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_1558_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1559_ = lean_unbox(v_val_1530_);
v___x_1560_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
lean_inc_ref(v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1562_, 0, v_val_1512_);
lean_ctor_set(v___x_1562_, 1, v___x_1535_);
lean_ctor_set(v___x_1562_, 2, v___x_1539_);
lean_ctor_set(v___x_1562_, 3, v___x_1542_);
lean_ctor_set(v___x_1562_, 4, v___x_1544_);
lean_ctor_set(v___x_1562_, 5, v___x_1541_);
lean_ctor_set(v___x_1562_, 6, v___x_1546_);
lean_ctor_set(v___x_1562_, 7, v___x_1547_);
lean_ctor_set(v___x_1562_, 8, v___x_1548_);
lean_ctor_set(v___x_1562_, 9, v___x_1549_);
lean_ctor_set(v___x_1562_, 10, v___x_1550_);
lean_ctor_set(v___x_1562_, 11, v___x_1553_);
lean_ctor_set(v___x_1562_, 12, v___x_1555_);
lean_ctor_set(v___x_1562_, 13, v___x_1556_);
lean_ctor_set(v___x_1562_, 14, v___x_1557_);
lean_ctor_set(v___x_1562_, 15, v___x_1558_);
lean_ctor_set(v___x_1562_, 16, v___x_1560_);
lean_ctor_set(v___x_1562_, 17, v___x_1561_);
lean_ctor_set(v___x_1562_, 18, v___x_1558_);
lean_ctor_set(v___x_1562_, 19, v___x_1560_);
lean_ctor_set(v___x_1562_, 20, v___x_1561_);
v___x_1563_ = lean_unbox(v_val_1530_);
lean_dec(v_val_1530_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*21, v___x_1563_);
v___x_1564_ = l_Lake_findLeanInstall_x3f();
v___x_1565_ = l_Lake_LakeInstall_ofLean(v___x_1562_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1565_);
v___x_1567_ = v___x_1532_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1564_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1510_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
return v___x_1569_;
}
}
}
}
}
v___jp_1518_:
{
uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1519_ = 1;
v___x_1520_ = l_Lake_LeanInstall_get(v_val_1512_, v___x_1519_);
lean_inc_ref(v___x_1520_);
v___x_1521_ = l_Lake_LakeInstall_ofLean(v___x_1520_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1520_);
v___x_1523_ = v___x_1514_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1520_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1521_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1510_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
return v___x_1526_;
}
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v___x_1511_);
v___x_1573_ = l_Lake_findLeanInstall_x3f();
v___x_1574_ = l_Lake_findLakeInstall_x3f();
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1510_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lake_findInstall_x3f();
return v_res_1578_;
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
