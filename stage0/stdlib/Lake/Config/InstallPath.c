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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
static const lean_string_object l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanshared"};
static const lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3 = (const lean_object*)&l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3_value;
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
static const lean_string_object l_Lake_leanSharedDynlibs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "libleanshared."};
static const lean_object* l_Lake_leanSharedDynlibs___closed__6 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__6_value;
static lean_once_cell_t l_Lake_leanSharedDynlibs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_leanSharedDynlibs___closed__7;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "libInit_shared.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__8 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__8_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "libleanshared_1.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__9 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__9_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "libleanshared_2.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__10 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__10_value;
static const lean_string_object l_Lake_leanSharedDynlibs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "libleanshared.dll"};
static const lean_object* l_Lake_leanSharedDynlibs___closed__11 = (const lean_object*)&l_Lake_leanSharedDynlibs___closed__11_value;
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
uint32_t v___y_15_; lean_object* v___x_20_; uint8_t v_decide_21_; 
v___x_20_ = lean_string_utf8_byte_size(v_s_12_);
v_decide_21_ = lean_nat_dec_eq(v_p_13_, v___x_20_);
if (v_decide_21_ == 0)
{
uint32_t v___x_22_; uint8_t v___y_24_; uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_22_ = lean_string_utf8_get_fast(v_s_12_, v_p_13_);
v___x_27_ = 65;
v___x_28_ = lean_uint32_dec_le(v___x_27_, v___x_22_);
if (v___x_28_ == 0)
{
v___y_24_ = v___x_28_;
goto v___jp_23_;
}
else
{
uint32_t v___x_29_; uint8_t v___x_30_; 
v___x_29_ = 90;
v___x_30_ = lean_uint32_dec_le(v___x_22_, v___x_29_);
v___y_24_ = v___x_30_;
goto v___jp_23_;
}
v___jp_23_:
{
if (v___y_24_ == 0)
{
v___y_15_ = v___x_22_;
goto v___jp_14_;
}
else
{
uint32_t v___x_25_; uint32_t v___x_26_; 
v___x_25_ = 32;
v___x_26_ = lean_uint32_add(v___x_22_, v___x_25_);
v___y_15_ = v___x_26_;
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
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* v_o_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__11));
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_79_, v___x_81_);
v___x_83_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_82_, v___x_80_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__23));
v___x_85_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_82_, v___x_84_);
lean_dec_ref(v___x_82_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(v___x_83_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v___x_82_);
v___x_89_ = lean_box(v___x_83_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_94_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_95_ = l_System_FilePath_join(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_98_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_99_ = l_System_FilePath_join(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__5(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__4, &l_Lake_instInhabitedElanInstall_default___closed__4_once, _init_l_Lake_instInhabitedElanInstall_default___closed__4);
v___x_101_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_102_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
lean_ctor_set(v___x_103_, 2, v___x_101_);
lean_ctor_set(v___x_103_, 3, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__5, &l_Lake_instInhabitedElanInstall_default___closed__5_once, _init_l_Lake_instInhabitedElanInstall_default___closed__5);
return v___x_104_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lake_instInhabitedElanInstall_default;
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* v_a_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_nat_to_int(v_a_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(8u);
v___x_122_ = lean_nat_to_int(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(10u);
v___x_136_ = lean_nat_to_int(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(17u);
v___x_141_ = lean_nat_to_int(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__0));
v___x_144_ = lean_string_length(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__21, &l_Lake_instReprElanInstall_repr___redArg___closed__21_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__21);
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* v_x_151_){
_start:
{
lean_object* v_home_152_; lean_object* v_elan_153_; lean_object* v_binDir_154_; lean_object* v_toolchainsDir_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_home_152_ = lean_ctor_get(v_x_151_, 0);
lean_inc_ref(v_home_152_);
v_elan_153_ = lean_ctor_get(v_x_151_, 1);
lean_inc_ref(v_elan_153_);
v_binDir_154_ = lean_ctor_get(v_x_151_, 2);
lean_inc_ref(v_binDir_154_);
v_toolchainsDir_155_ = lean_ctor_get(v_x_151_, 3);
lean_inc_ref(v_toolchainsDir_155_);
lean_dec_ref(v_x_151_);
v___x_156_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_157_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_158_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_161_ = l_String_quote(v_home_152_);
v___x_162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_160_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Repr_addAppParen(v___x_163_, v___x_159_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_158_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_157_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_box(1);
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__13));
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_156_);
v___x_176_ = l_String_quote(v_elan_153_);
v___x_177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_160_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Repr_addAppParen(v___x_178_, v___x_159_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_158_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_166_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_175_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_169_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_171_);
v___x_185_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_156_);
v___x_188_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_189_ = l_String_quote(v_binDir_154_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_160_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = l_Repr_addAppParen(v___x_191_, v___x_159_);
v___x_193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_188_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_166_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_187_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_169_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_171_);
v___x_198_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__18));
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_156_);
v___x_201_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_202_ = l_String_quote(v_toolchainsDir_155_);
v___x_203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_160_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v___x_159_);
v___x_206_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_201_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*1, v___x_166_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_200_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_210_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_208_);
v___x_212_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*1, v___x_166_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* v_x_216_, lean_object* v_prec_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lake_instReprElanInstall_repr___redArg(v_x_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* v_x_219_, lean_object* v_prec_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_instReprElanInstall_repr(v_x_219_, v_prec_220_);
lean_dec(v_prec_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* v_toolchain_226_, lean_object* v_acc_227_, lean_object* v_pos_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_string_utf8_at_end(v_toolchain_226_, v_pos_228_);
if (v___x_229_ == 0)
{
uint32_t v_c_230_; lean_object* v_pos_x27_231_; uint32_t v___x_232_; uint8_t v___x_233_; 
v_c_230_ = lean_string_utf8_get_fast(v_toolchain_226_, v_pos_228_);
v_pos_x27_231_ = lean_string_utf8_next_fast(v_toolchain_226_, v_pos_228_);
lean_dec(v_pos_228_);
v___x_232_ = 47;
v___x_233_ = lean_uint32_dec_eq(v_c_230_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 58;
v___x_235_ = lean_uint32_dec_eq(v_c_230_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_string_push(v_acc_227_, v_c_230_);
v_acc_227_ = v___x_236_;
v_pos_228_ = v_pos_x27_231_;
goto _start;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0));
v___x_239_ = lean_string_append(v_acc_227_, v___x_238_);
v_acc_227_ = v___x_239_;
v_pos_228_ = v_pos_x27_231_;
goto _start;
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1));
v___x_242_ = lean_string_append(v_acc_227_, v___x_241_);
v_acc_227_ = v___x_242_;
v_pos_228_ = v_pos_x27_231_;
goto _start;
}
}
else
{
lean_dec(v_pos_228_);
return v_acc_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* v_toolchain_244_, lean_object* v_acc_245_, lean_object* v_pos_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_244_, v_acc_245_, v_pos_246_);
lean_dec_ref(v_toolchain_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* v_toolchain_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_248_, v___x_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* v_toolchain_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lake_toolchain2Dir(v_toolchain_252_);
lean_dec_ref(v_toolchain_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* v_toolchain_254_, lean_object* v_elan_255_){
_start:
{
lean_object* v_toolchainsDir_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_toolchainsDir_256_ = lean_ctor_get(v_elan_255_, 3);
lean_inc_ref(v_toolchainsDir_256_);
lean_dec_ref(v_elan_255_);
v___x_257_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_254_, v___x_257_, v___x_258_);
v___x_260_ = l_System_FilePath_join(v_toolchainsDir_256_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* v_toolchain_261_, lean_object* v_elan_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_261_, v_elan_262_);
lean_dec_ref(v_toolchain_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* v_sysroot_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_266_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_267_ = l_System_FilePath_join(v_sysroot_265_, v___x_266_);
v___x_268_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_269_ = l_System_FilePath_join(v___x_267_, v___x_268_);
v___x_270_ = l_System_FilePath_exeExtension;
v___x_271_ = l_System_FilePath_addExtension(v___x_269_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object* v_sysroot_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_274_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_275_ = l_System_FilePath_join(v_sysroot_273_, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lake_leanirExe___closed__0));
v___x_277_ = l_System_FilePath_join(v___x_275_, v___x_276_);
v___x_278_ = l_System_FilePath_exeExtension;
v___x_279_ = l_System_FilePath_addExtension(v___x_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_283_ = l_System_FilePath_join(v_sysroot_281_, v___x_282_);
v___x_284_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_285_ = l_System_FilePath_join(v___x_283_, v___x_284_);
v___x_286_ = l_System_FilePath_exeExtension;
v___x_287_ = l_System_FilePath_addExtension(v___x_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_290_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_291_ = l_System_FilePath_join(v_sysroot_289_, v___x_290_);
v___x_292_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_293_ = l_System_FilePath_join(v___x_291_, v___x_292_);
v___x_294_ = l_System_FilePath_exeExtension;
v___x_295_ = l_System_FilePath_addExtension(v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_298_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_299_ = l_System_FilePath_join(v_sysroot_297_, v___x_298_);
v___x_300_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_301_ = l_System_FilePath_join(v___x_299_, v___x_300_);
v___x_302_ = l_System_FilePath_exeExtension;
v___x_303_ = l_System_FilePath_addExtension(v___x_301_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_307_ = l_System_FilePath_join(v_sysroot_305_, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_309_ = l_System_FilePath_join(v___x_307_, v___x_308_);
v___x_310_ = l_System_FilePath_exeExtension;
v___x_311_ = l_System_FilePath_addExtension(v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_System_Platform_isWindows;
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_316_ = l_System_FilePath_join(v_sysroot_313_, v___x_315_);
v___x_317_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_318_ = l_System_FilePath_join(v___x_316_, v___x_317_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_320_ = l_System_FilePath_join(v_sysroot_313_, v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib(lean_object* v_sysroot_324_, lean_object* v_name_325_, lean_object* v_deps_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_327_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_328_ = l_System_FilePath_join(v_sysroot_324_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_330_ = lean_string_append(v___x_329_, v_name_325_);
v___x_331_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0));
v___x_332_ = lean_string_append(v___x_330_, v___x_331_);
v___x_333_ = l_System_FilePath_join(v___x_328_, v___x_332_);
v___x_334_ = 0;
v___x_335_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_336_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_336_, 0, v___x_333_);
lean_ctor_set(v___x_336_, 1, v_name_325_);
lean_ctor_set(v___x_336_, 2, v_deps_326_);
lean_ctor_set(v___x_336_, 3, v___x_335_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*4, v___x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg(lean_object* v_sysroot_338_, lean_object* v_name_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_340_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_341_ = l_System_FilePath_join(v_sysroot_338_, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_343_ = l_System_FilePath_join(v___x_341_, v___x_342_);
v___x_344_ = lean_string_append(v___x_340_, v_name_339_);
v___x_345_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_346_ = lean_string_append(v___x_344_, v___x_345_);
v___x_347_ = l_Lake_sharedLibExt;
v___x_348_ = lean_string_append(v___x_346_, v___x_347_);
v___x_349_ = l_System_FilePath_join(v___x_343_, v___x_348_);
v___x_350_ = 0;
v___x_351_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_352_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_352_, 0, v___x_349_);
lean_ctor_set(v___x_352_, 1, v_name_339_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set(v___x_352_, 3, v___x_351_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*4, v___x_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(lean_object* v_sysroot_353_, lean_object* v_name_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_356_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_357_ = l_System_FilePath_join(v_sysroot_353_, v___x_356_);
v___x_358_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_359_ = l_System_FilePath_join(v___x_357_, v___x_358_);
v___x_360_ = lean_string_append(v___x_356_, v_name_354_);
v___x_361_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
v___x_363_ = l_Lake_sharedLibExt;
v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
v___x_365_ = l_System_FilePath_join(v___x_359_, v___x_364_);
v___x_366_ = 0;
v___x_367_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_368_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_368_, 0, v___x_365_);
lean_ctor_set(v___x_368_, 1, v_name_354_);
lean_ctor_set(v___x_368_, 2, v___x_367_);
lean_ctor_set(v___x_368_, 3, v___x_367_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*4, v___x_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___boxed(lean_object* v_sysroot_369_, lean_object* v_name_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(v_sysroot_369_, v_name_370_, v_x_371_);
lean_dec_ref(v_x_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs(lean_object* v_f_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_init_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_lean1_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_lean2_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_lean_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_378_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_379_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
lean_inc_ref_n(v_f_377_, 3);
v_init_380_ = lean_apply_2(v_f_377_, v___x_378_, v___x_379_);
v___x_381_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_mk_empty_array_with_capacity(v___x_382_);
lean_inc_ref_n(v_init_380_, 3);
v___x_384_ = lean_array_push(v___x_383_, v_init_380_);
v_lean1_385_ = lean_apply_2(v_f_377_, v___x_381_, v___x_384_);
v___x_386_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_387_ = lean_unsigned_to_nat(2u);
v___x_388_ = lean_mk_empty_array_with_capacity(v___x_387_);
lean_inc_ref_n(v_lean1_385_, 2);
v___x_389_ = lean_array_push(v___x_388_, v_lean1_385_);
v___x_390_ = lean_array_push(v___x_389_, v_init_380_);
v_lean2_391_ = lean_apply_2(v_f_377_, v___x_386_, v___x_390_);
v___x_392_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_393_ = lean_unsigned_to_nat(3u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
lean_inc_ref(v_lean2_391_);
v___x_395_ = lean_array_push(v___x_394_, v_lean2_391_);
v___x_396_ = lean_array_push(v___x_395_, v_lean1_385_);
v___x_397_ = lean_array_push(v___x_396_, v_init_380_);
v_lean_398_ = lean_apply_2(v_f_377_, v___x_392_, v___x_397_);
v___x_399_ = lean_unsigned_to_nat(4u);
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_399_);
v___x_401_ = lean_array_push(v___x_400_, v_lean_398_);
v___x_402_ = lean_array_push(v___x_401_, v_lean2_391_);
v___x_403_ = lean_array_push(v___x_402_, v_lean1_385_);
v___x_404_ = lean_array_push(v___x_403_, v_init_380_);
return v___x_404_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = l_Lake_sharedLibExt;
v___x_407_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__0));
v___x_408_ = lean_string_append(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = l_Lake_sharedLibExt;
v___x_411_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__2));
v___x_412_ = lean_string_append(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__5(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = l_Lake_sharedLibExt;
v___x_415_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__4));
v___x_416_ = lean_string_append(v___x_415_, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__7(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = l_Lake_sharedLibExt;
v___x_419_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__6));
v___x_420_ = lean_string_append(v___x_419_, v___x_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlibs(lean_object* v_sysroot_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = l_System_Platform_isWindows;
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_init_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_lean1_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_lean2_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_lean_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_427_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_428_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_429_ = l_System_FilePath_join(v_sysroot_425_, v___x_428_);
v___x_430_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_431_ = l_System_FilePath_join(v___x_429_, v___x_430_);
v___x_432_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__1, &l_Lake_leanSharedDynlibs___closed__1_once, _init_l_Lake_leanSharedDynlibs___closed__1);
lean_inc_ref_n(v___x_431_, 3);
v___x_433_ = l_System_FilePath_join(v___x_431_, v___x_432_);
v___x_434_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v_init_435_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_435_, 0, v___x_433_);
lean_ctor_set(v_init_435_, 1, v___x_427_);
lean_ctor_set(v_init_435_, 2, v___x_434_);
lean_ctor_set(v_init_435_, 3, v___x_434_);
lean_ctor_set_uint8(v_init_435_, sizeof(void*)*4, v___x_426_);
v___x_436_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_437_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__3, &l_Lake_leanSharedDynlibs___closed__3_once, _init_l_Lake_leanSharedDynlibs___closed__3);
v___x_438_ = l_System_FilePath_join(v___x_431_, v___x_437_);
v_lean1_439_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_439_, 0, v___x_438_);
lean_ctor_set(v_lean1_439_, 1, v___x_436_);
lean_ctor_set(v_lean1_439_, 2, v___x_434_);
lean_ctor_set(v_lean1_439_, 3, v___x_434_);
lean_ctor_set_uint8(v_lean1_439_, sizeof(void*)*4, v___x_426_);
v___x_440_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_441_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__5, &l_Lake_leanSharedDynlibs___closed__5_once, _init_l_Lake_leanSharedDynlibs___closed__5);
v___x_442_ = l_System_FilePath_join(v___x_431_, v___x_441_);
v_lean2_443_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_443_, 0, v___x_442_);
lean_ctor_set(v_lean2_443_, 1, v___x_440_);
lean_ctor_set(v_lean2_443_, 2, v___x_434_);
lean_ctor_set(v_lean2_443_, 3, v___x_434_);
lean_ctor_set_uint8(v_lean2_443_, sizeof(void*)*4, v___x_426_);
v___x_444_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_445_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__7, &l_Lake_leanSharedDynlibs___closed__7_once, _init_l_Lake_leanSharedDynlibs___closed__7);
v___x_446_ = l_System_FilePath_join(v___x_431_, v___x_445_);
v_lean_447_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_447_, 0, v___x_446_);
lean_ctor_set(v_lean_447_, 1, v___x_444_);
lean_ctor_set(v_lean_447_, 2, v___x_434_);
lean_ctor_set(v_lean_447_, 3, v___x_434_);
lean_ctor_set_uint8(v_lean_447_, sizeof(void*)*4, v___x_426_);
v___x_448_ = lean_unsigned_to_nat(4u);
v___x_449_ = lean_mk_empty_array_with_capacity(v___x_448_);
v___x_450_ = lean_array_push(v___x_449_, v_lean_447_);
v___x_451_ = lean_array_push(v___x_450_, v_lean2_443_);
v___x_452_ = lean_array_push(v___x_451_, v_lean1_439_);
v___x_453_ = lean_array_push(v___x_452_, v_init_435_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v_init_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_lean1_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_lean2_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_lean_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_454_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_455_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_456_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_457_ = l_System_FilePath_join(v_sysroot_425_, v___x_456_);
v___x_458_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__8));
lean_inc_ref_n(v___x_457_, 3);
v___x_459_ = l_System_FilePath_join(v___x_457_, v___x_458_);
v___x_460_ = 0;
v_init_461_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_461_, 0, v___x_459_);
lean_ctor_set(v_init_461_, 1, v___x_454_);
lean_ctor_set(v_init_461_, 2, v___x_455_);
lean_ctor_set(v_init_461_, 3, v___x_455_);
lean_ctor_set_uint8(v_init_461_, sizeof(void*)*4, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_mk_empty_array_with_capacity(v___x_463_);
lean_inc_ref_n(v_init_461_, 3);
v___x_465_ = lean_array_push(v___x_464_, v_init_461_);
v___x_466_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__9));
v___x_467_ = l_System_FilePath_join(v___x_457_, v___x_466_);
v_lean1_468_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_468_, 0, v___x_467_);
lean_ctor_set(v_lean1_468_, 1, v___x_462_);
lean_ctor_set(v_lean1_468_, 2, v___x_465_);
lean_ctor_set(v_lean1_468_, 3, v___x_455_);
lean_ctor_set_uint8(v_lean1_468_, sizeof(void*)*4, v___x_460_);
v___x_469_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_470_ = lean_unsigned_to_nat(2u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
lean_inc_ref_n(v_lean1_468_, 2);
v___x_472_ = lean_array_push(v___x_471_, v_lean1_468_);
v___x_473_ = lean_array_push(v___x_472_, v_init_461_);
v___x_474_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__10));
v___x_475_ = l_System_FilePath_join(v___x_457_, v___x_474_);
v_lean2_476_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_476_, 0, v___x_475_);
lean_ctor_set(v_lean2_476_, 1, v___x_469_);
lean_ctor_set(v_lean2_476_, 2, v___x_473_);
lean_ctor_set(v_lean2_476_, 3, v___x_455_);
lean_ctor_set_uint8(v_lean2_476_, sizeof(void*)*4, v___x_460_);
v___x_477_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_478_ = lean_unsigned_to_nat(3u);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_478_);
lean_inc_ref(v_lean2_476_);
v___x_480_ = lean_array_push(v___x_479_, v_lean2_476_);
v___x_481_ = lean_array_push(v___x_480_, v_lean1_468_);
v___x_482_ = lean_array_push(v___x_481_, v_init_461_);
v___x_483_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__11));
v___x_484_ = l_System_FilePath_join(v___x_457_, v___x_483_);
v_lean_485_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_485_, 0, v___x_484_);
lean_ctor_set(v_lean_485_, 1, v___x_477_);
lean_ctor_set(v_lean_485_, 2, v___x_482_);
lean_ctor_set(v_lean_485_, 3, v___x_455_);
lean_ctor_set_uint8(v_lean_485_, sizeof(void*)*4, v___x_460_);
v___x_486_ = lean_unsigned_to_nat(4u);
v___x_487_ = lean_mk_empty_array_with_capacity(v___x_486_);
v___x_488_ = lean_array_push(v___x_487_, v_lean_485_);
v___x_489_ = lean_array_push(v___x_488_, v_lean2_476_);
v___x_490_ = lean_array_push(v___x_489_, v_lean1_468_);
v___x_491_ = lean_array_push(v___x_490_, v_init_461_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlib(lean_object* v_sysroot_492_){
_start:
{
lean_object* v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = l_Lake_leanSharedDynlibs(v_sysroot_492_);
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_array_uget(v___x_493_, v___x_494_);
lean_dec_ref(v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = l_Lake_sharedLibExt;
v___x_498_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_499_ = l_System_FilePath_addExtension(v___x_498_, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_500_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = l_Lake_sharedLibExt;
v___x_503_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_504_ = l_System_FilePath_addExtension(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_505_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_508_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_509_ = l_System_FilePath_join(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_511_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
v___x_512_ = l_System_FilePath_join(v___x_511_, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_514_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_515_ = l_System_FilePath_join(v___x_514_, v___x_513_);
return v___x_515_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_517_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_518_ = l_System_FilePath_join(v___x_517_, v___x_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_521_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_522_ = l_System_FilePath_join(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__7(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_524_ = l_Lake_leanExe(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__8(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_526_ = l_Lake_leanirExe(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__9(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_528_ = l_Lake_leancExe(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__10(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_530_ = l_Lake_leantarExe(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__11(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_532_ = l_Lake_leanSharedDynlibs(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__12(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_534_ = l_Lake_leanSharedDynlib(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__16(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_539_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_540_ = lean_array_push(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__17(void){
_start:
{
uint8_t v___x_541_; lean_object* v___x_542_; 
v___x_541_ = 1;
v___x_542_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__18(void){
_start:
{
uint8_t v___x_543_; lean_object* v___x_544_; 
v___x_543_ = 0;
v___x_544_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__19(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_545_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_546_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_547_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_548_ = 1;
v___x_549_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_550_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_551_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__12, &l_Lake_instInhabitedLeanInstall_default___closed__12_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__12);
v___x_552_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_553_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__10, &l_Lake_instInhabitedLeanInstall_default___closed__10_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__10);
v___x_554_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__9, &l_Lake_instInhabitedLeanInstall_default___closed__9_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__9);
v___x_555_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__8, &l_Lake_instInhabitedLeanInstall_default___closed__8_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__8);
v___x_556_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__7, &l_Lake_instInhabitedLeanInstall_default___closed__7_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__7);
v___x_557_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_558_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_559_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
v___x_560_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_561_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__2, &l_Lake_instInhabitedLeanInstall_default___closed__2_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__2);
v___x_562_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_563_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_560_);
lean_ctor_set(v___x_563_, 4, v___x_559_);
lean_ctor_set(v___x_563_, 5, v___x_558_);
lean_ctor_set(v___x_563_, 6, v___x_557_);
lean_ctor_set(v___x_563_, 7, v___x_556_);
lean_ctor_set(v___x_563_, 8, v___x_555_);
lean_ctor_set(v___x_563_, 9, v___x_554_);
lean_ctor_set(v___x_563_, 10, v___x_553_);
lean_ctor_set(v___x_563_, 11, v___x_552_);
lean_ctor_set(v___x_563_, 12, v___x_551_);
lean_ctor_set(v___x_563_, 13, v___x_550_);
lean_ctor_set(v___x_563_, 14, v___x_549_);
lean_ctor_set(v___x_563_, 15, v___x_547_);
lean_ctor_set(v___x_563_, 16, v___x_546_);
lean_ctor_set(v___x_563_, 17, v___x_545_);
lean_ctor_set(v___x_563_, 18, v___x_547_);
lean_ctor_set(v___x_563_, 19, v___x_546_);
lean_ctor_set(v___x_563_, 20, v___x_545_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*21, v___x_548_);
return v___x_563_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
return v___x_564_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_dec(v_x_566_);
return v_x_567_;
}
else
{
lean_object* v_head_569_; lean_object* v_tail_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_581_; 
v_head_569_ = lean_ctor_get(v_x_568_, 0);
v_tail_570_ = lean_ctor_get(v_x_568_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_581_ == 0)
{
v___x_572_ = v_x_568_;
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_tail_570_);
lean_inc(v_head_569_);
lean_dec(v_x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
lean_inc(v_x_566_);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 5);
lean_ctor_set(v___x_572_, 1, v_x_566_);
lean_ctor_set(v___x_572_, 0, v_x_567_);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_x_567_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_x_566_);
v___x_575_ = v_reuseFailAlloc_580_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = l_String_quote(v_head_569_);
v___x_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_575_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v_x_567_ = v___x_578_;
v_x_568_ = v_tail_570_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_dec(v_x_582_);
return v_x_583_;
}
else
{
lean_object* v_head_585_; lean_object* v_tail_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_597_; 
v_head_585_ = lean_ctor_get(v_x_584_, 0);
v_tail_586_ = lean_ctor_get(v_x_584_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_597_ == 0)
{
v___x_588_ = v_x_584_;
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_tail_586_);
lean_inc(v_head_585_);
lean_dec(v_x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
lean_inc(v_x_582_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 5);
lean_ctor_set(v___x_588_, 1, v_x_582_);
lean_ctor_set(v___x_588_, 0, v_x_583_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_x_583_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_x_582_);
v___x_591_ = v_reuseFailAlloc_596_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = l_String_quote(v_head_585_);
v___x_593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(v_x_582_, v___x_594_, v_tail_586_);
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(lean_object* v___y_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_String_quote(v___y_598_);
v___x_600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v___x_603_; 
lean_dec(v_x_602_);
v___x_603_ = lean_box(0);
return v___x_603_;
}
else
{
lean_object* v_tail_604_; 
v_tail_604_ = lean_ctor_get(v_x_601_, 1);
if (lean_obj_tag(v_tail_604_) == 0)
{
lean_object* v_head_605_; lean_object* v___x_606_; 
lean_dec(v_x_602_);
v_head_605_ = lean_ctor_get(v_x_601_, 0);
lean_inc(v_head_605_);
lean_dec_ref_known(v_x_601_, 2);
v___x_606_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_605_);
return v___x_606_;
}
else
{
lean_object* v_head_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc(v_tail_604_);
v_head_607_ = lean_ctor_get(v_x_601_, 0);
lean_inc(v_head_607_);
lean_dec_ref_known(v_x_601_, 2);
v___x_608_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_607_);
v___x_609_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(v_x_602_, v___x_608_, v_tail_604_);
return v___x_609_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0));
v___x_616_ = lean_string_length(v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3);
v___x_618_ = lean_nat_to_int(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(lean_object* v_xs_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_array_get_size(v_xs_626_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_630_ = lean_array_to_list(v_xs_626_);
v___x_631_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_632_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(v___x_630_, v___x_631_);
v___x_633_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_634_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_632_);
v___x_636_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_633_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Std_Format_fill(v___x_638_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; 
lean_dec_ref(v_xs_626_);
v___x_640_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_dec(v_x_641_);
return v_x_642_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_655_; 
v_head_644_ = lean_ctor_get(v_x_643_, 0);
v_tail_645_ = lean_ctor_get(v_x_643_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_655_ == 0)
{
v___x_647_ = v_x_643_;
v_isShared_648_ = v_isSharedCheck_655_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_tail_645_);
lean_inc(v_head_644_);
lean_dec(v_x_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_655_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
lean_inc(v_x_641_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 5);
lean_ctor_set(v___x_647_, 1, v_x_641_);
lean_ctor_set(v___x_647_, 0, v_x_642_);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_x_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_x_641_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = l_Lake_instReprDynlib_repr___redArg(v_head_644_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v_x_642_ = v___x_652_;
v_x_643_ = v_tail_645_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_dec(v_x_656_);
return v_x_657_;
}
else
{
lean_object* v_head_659_; lean_object* v_tail_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_670_; 
v_head_659_ = lean_ctor_get(v_x_658_, 0);
v_tail_660_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_670_ == 0)
{
v___x_662_ = v_x_658_;
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_tail_660_);
lean_inc(v_head_659_);
lean_dec(v_x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
lean_inc(v_x_656_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 5);
lean_ctor_set(v___x_662_, 1, v_x_656_);
lean_ctor_set(v___x_662_, 0, v_x_657_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_x_656_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = l_Lake_instReprDynlib_repr___redArg(v_head_659_);
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(v_x_656_, v___x_667_, v_tail_660_);
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_673_; 
lean_dec(v_x_672_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
else
{
lean_object* v_tail_674_; 
v_tail_674_ = lean_ctor_get(v_x_671_, 1);
if (lean_obj_tag(v_tail_674_) == 0)
{
lean_object* v_head_675_; lean_object* v___x_676_; 
lean_dec(v_x_672_);
v_head_675_ = lean_ctor_get(v_x_671_, 0);
lean_inc(v_head_675_);
lean_dec_ref_known(v_x_671_, 2);
v___x_676_ = l_Lake_instReprDynlib_repr___redArg(v_head_675_);
return v___x_676_;
}
else
{
lean_object* v_head_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_inc(v_tail_674_);
v_head_677_ = lean_ctor_get(v_x_671_, 0);
lean_inc(v_head_677_);
lean_dec_ref_known(v_x_671_, 2);
v___x_678_ = l_Lake_instReprDynlib_repr___redArg(v_head_677_);
v___x_679_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_672_, v___x_678_, v_tail_674_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_681_ = lean_array_get_size(v_xs_680_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_eq(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_684_ = lean_array_to_list(v_xs_680_);
v___x_685_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_686_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_684_, v___x_685_);
v___x_687_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_688_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_686_);
v___x_690_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_687_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Std_Format_fill(v___x_692_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; 
lean_dec_ref(v_xs_680_);
v___x_694_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_694_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(11u);
v___x_705_ = lean_nat_to_int(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(14u);
v___x_716_ = lean_nat_to_int(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(16u);
v___x_724_ = lean_nat_to_int(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(9u);
v___x_732_ = lean_nat_to_int(v___x_731_);
return v___x_732_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(6u);
v___x_744_ = lean_nat_to_int(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(12u);
v___x_751_ = lean_nat_to_int(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(19u);
v___x_759_ = lean_nat_to_int(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(21u);
v___x_770_ = lean_nat_to_int(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_774_){
_start:
{
lean_object* v_sysroot_775_; lean_object* v_githash_776_; lean_object* v_srcDir_777_; lean_object* v_leanLibDir_778_; lean_object* v_includeDir_779_; lean_object* v_systemLibDir_780_; lean_object* v_binDir_781_; lean_object* v_lean_782_; lean_object* v_leanir_783_; lean_object* v_leanc_784_; lean_object* v_leantar_785_; lean_object* v_sharedDynlibs_786_; lean_object* v_sharedDynlib_787_; lean_object* v_ar_788_; lean_object* v_cc_789_; uint8_t v_customCc_790_; lean_object* v_cFlags_791_; lean_object* v_linkStaticFlags_792_; lean_object* v_linkSharedFlags_793_; lean_object* v_ccFlags_794_; lean_object* v_ccLinkStaticFlags_795_; lean_object* v_ccLinkSharedFlags_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_sysroot_775_ = lean_ctor_get(v_x_774_, 0);
lean_inc_ref(v_sysroot_775_);
v_githash_776_ = lean_ctor_get(v_x_774_, 1);
lean_inc_ref(v_githash_776_);
v_srcDir_777_ = lean_ctor_get(v_x_774_, 2);
lean_inc_ref(v_srcDir_777_);
v_leanLibDir_778_ = lean_ctor_get(v_x_774_, 3);
lean_inc_ref(v_leanLibDir_778_);
v_includeDir_779_ = lean_ctor_get(v_x_774_, 4);
lean_inc_ref(v_includeDir_779_);
v_systemLibDir_780_ = lean_ctor_get(v_x_774_, 5);
lean_inc_ref(v_systemLibDir_780_);
v_binDir_781_ = lean_ctor_get(v_x_774_, 6);
lean_inc_ref(v_binDir_781_);
v_lean_782_ = lean_ctor_get(v_x_774_, 7);
lean_inc_ref(v_lean_782_);
v_leanir_783_ = lean_ctor_get(v_x_774_, 8);
lean_inc_ref(v_leanir_783_);
v_leanc_784_ = lean_ctor_get(v_x_774_, 9);
lean_inc_ref(v_leanc_784_);
v_leantar_785_ = lean_ctor_get(v_x_774_, 10);
lean_inc_ref(v_leantar_785_);
v_sharedDynlibs_786_ = lean_ctor_get(v_x_774_, 11);
lean_inc_ref(v_sharedDynlibs_786_);
v_sharedDynlib_787_ = lean_ctor_get(v_x_774_, 12);
lean_inc_ref(v_sharedDynlib_787_);
v_ar_788_ = lean_ctor_get(v_x_774_, 13);
lean_inc_ref(v_ar_788_);
v_cc_789_ = lean_ctor_get(v_x_774_, 14);
lean_inc_ref(v_cc_789_);
v_customCc_790_ = lean_ctor_get_uint8(v_x_774_, sizeof(void*)*21);
v_cFlags_791_ = lean_ctor_get(v_x_774_, 15);
lean_inc_ref(v_cFlags_791_);
v_linkStaticFlags_792_ = lean_ctor_get(v_x_774_, 16);
lean_inc_ref(v_linkStaticFlags_792_);
v_linkSharedFlags_793_ = lean_ctor_get(v_x_774_, 17);
lean_inc_ref(v_linkSharedFlags_793_);
v_ccFlags_794_ = lean_ctor_get(v_x_774_, 18);
lean_inc_ref(v_ccFlags_794_);
v_ccLinkStaticFlags_795_ = lean_ctor_get(v_x_774_, 19);
lean_inc_ref(v_ccLinkStaticFlags_795_);
v_ccLinkSharedFlags_796_ = lean_ctor_get(v_x_774_, 20);
lean_inc_ref(v_ccLinkSharedFlags_796_);
lean_dec_ref(v_x_774_);
v___x_797_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_798_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_799_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_802_ = l_String_quote(v_sysroot_775_);
v___x_803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_801_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Repr_addAppParen(v___x_804_, v___x_800_);
v___x_806_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_799_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = 0;
v___x_808_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*1, v___x_807_);
v___x_809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_798_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_box(1);
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_797_);
v___x_817_ = l_String_quote(v_githash_776_);
v___x_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_799_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v___x_807_);
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_816_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_810_);
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_812_);
v___x_824_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_797_);
v___x_827_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_828_ = l_String_quote(v_srcDir_777_);
v___x_829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_801_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Repr_addAppParen(v___x_830_, v___x_800_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_827_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*1, v___x_807_);
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_826_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_810_);
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___x_812_);
v___x_837_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_797_);
v___x_840_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_841_ = l_String_quote(v_leanLibDir_778_);
v___x_842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
v___x_843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_801_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Repr_addAppParen(v___x_843_, v___x_800_);
v___x_845_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_840_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_807_);
v___x_847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_839_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_810_);
v___x_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_812_);
v___x_850_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v___x_797_);
v___x_853_ = l_String_quote(v_includeDir_779_);
v___x_854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_801_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Repr_addAppParen(v___x_855_, v___x_800_);
v___x_857_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_840_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*1, v___x_807_);
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_852_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_810_);
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_812_);
v___x_862_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_797_);
v___x_865_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_866_ = l_String_quote(v_systemLibDir_780_);
v___x_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_801_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Repr_addAppParen(v___x_868_, v___x_800_);
v___x_870_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_865_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*1, v___x_807_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_864_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_810_);
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_812_);
v___x_875_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_797_);
v___x_878_ = l_String_quote(v_binDir_781_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_801_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Repr_addAppParen(v___x_880_, v___x_800_);
v___x_882_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_827_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_807_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_877_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_810_);
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_812_);
v___x_887_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_797_);
v___x_890_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_891_ = l_String_quote(v_lean_782_);
v___x_892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_801_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Repr_addAppParen(v___x_893_, v___x_800_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_890_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_807_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_889_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_810_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_812_);
v___x_900_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_797_);
v___x_903_ = l_String_quote(v_leanir_783_);
v___x_904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_801_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Repr_addAppParen(v___x_905_, v___x_800_);
v___x_907_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_827_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1, v___x_807_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_902_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_810_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_812_);
v___x_912_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_797_);
v___x_915_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_916_ = l_String_quote(v_leanc_784_);
v___x_917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_801_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Repr_addAppParen(v___x_918_, v___x_800_);
v___x_920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_915_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*1, v___x_807_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_914_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_810_);
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_812_);
v___x_925_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_797_);
v___x_928_ = l_String_quote(v_leantar_785_);
v___x_929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_801_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Repr_addAppParen(v___x_930_, v___x_800_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_799_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_807_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_927_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_810_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_812_);
v___x_937_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_797_);
v___x_940_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_941_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_sharedDynlibs_786_);
v___x_942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_807_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_810_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_812_);
v___x_947_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_797_);
v___x_950_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_787_);
v___x_951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_865_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_807_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_949_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_810_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_812_);
v___x_956_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_797_);
v___x_959_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__27, &l_Lake_instReprLeanInstall_repr___redArg___closed__27_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27);
v___x_960_ = l_String_quote(v_ar_788_);
v___x_961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_801_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Repr_addAppParen(v___x_962_, v___x_800_);
v___x_964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_959_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_807_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_958_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_810_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_812_);
v___x_969_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__28));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_797_);
v___x_972_ = l_String_quote(v_cc_789_);
v___x_973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_801_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Repr_addAppParen(v___x_974_, v___x_800_);
v___x_976_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_959_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*1, v___x_807_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_971_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_810_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_812_);
v___x_981_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_797_);
v___x_984_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__31, &l_Lake_instReprLeanInstall_repr___redArg___closed__31_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31);
v___x_985_ = l_Bool_repr___redArg(v_customCc_790_);
v___x_986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*1, v___x_807_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_983_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_810_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_812_);
v___x_991_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__33));
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_797_);
v___x_994_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_cFlags_791_);
v___x_995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_827_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*1, v___x_807_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_993_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_810_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_812_);
v___x_1000_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__35));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_797_);
v___x_1003_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__36, &l_Lake_instReprLeanInstall_repr___redArg___closed__36_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36);
v___x_1004_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkStaticFlags_792_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_807_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1002_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_810_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_812_);
v___x_1010_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__38));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_797_);
v___x_1013_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkSharedFlags_793_);
v___x_1014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1003_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*1, v___x_807_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1012_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_810_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_812_);
v___x_1019_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__40));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_797_);
v___x_1022_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccFlags_794_);
v___x_1023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_799_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*1, v___x_807_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_810_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_812_);
v___x_1028_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__42));
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_797_);
v___x_1031_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__43, &l_Lake_instReprLeanInstall_repr___redArg___closed__43_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43);
v___x_1032_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkStaticFlags_795_);
v___x_1033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*1, v___x_807_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_810_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_812_);
v___x_1038_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__45));
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_797_);
v___x_1041_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkSharedFlags_796_);
v___x_1042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1031_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*1, v___x_807_);
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1040_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1046_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1044_);
v___x_1048_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1045_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*1, v___x_807_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_1052_, lean_object* v_prec_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_1055_, lean_object* v_prec_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lake_instReprLeanInstall_repr(v_x_1055_, v_prec_1056_);
lean_dec(v_prec_1056_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib(lean_object* v_self_1060_){
_start:
{
lean_object* v_sharedDynlib_1061_; lean_object* v_path_1062_; 
v_sharedDynlib_1061_ = lean_ctor_get(v_self_1060_, 12);
v_path_1062_ = lean_ctor_get(v_sharedDynlib_1061_, 0);
lean_inc_ref(v_path_1062_);
return v_path_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib___boxed(lean_object* v_self_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lake_LeanInstall_sharedLib(v_self_1063_);
lean_dec_ref(v_self_1063_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_initSharedLib(lean_object* v_self_1065_){
_start:
{
lean_object* v_sysroot_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_sysroot_1066_ = lean_ctor_get(v_self_1065_, 0);
lean_inc_ref(v_sysroot_1066_);
lean_dec_ref(v_self_1065_);
v___x_1067_ = l_Lake_leanSharedLibDir(v_sysroot_1066_);
v___x_1068_ = l_Lake_initSharedLib;
v___x_1069_ = l_System_FilePath_join(v___x_1067_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_1070_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = l_System_Platform_isWindows;
if (v___x_1071_ == 0)
{
lean_object* v_leanLibDir_1072_; lean_object* v_systemLibDir_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_leanLibDir_1072_ = lean_ctor_get(v_self_1070_, 3);
v_systemLibDir_1073_ = lean_ctor_get(v_self_1070_, 5);
v___x_1074_ = lean_box(0);
lean_inc_ref(v_systemLibDir_1073_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_systemLibDir_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc_ref(v_leanLibDir_1072_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_leanLibDir_1072_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_binDir_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_binDir_1077_ = lean_ctor_get(v_self_1070_, 6);
v___x_1078_ = lean_box(0);
lean_inc_ref(v_binDir_1077_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_binDir_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lake_LeanInstall_sharedLibPath(v_self_1080_);
lean_dec_ref(v_self_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_1082_){
_start:
{
uint8_t v_customCc_1083_; 
v_customCc_1083_ = lean_ctor_get_uint8(v_self_1082_, sizeof(void*)*21);
if (v_customCc_1083_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_box(0);
return v___x_1084_;
}
else
{
lean_object* v_cc_1085_; lean_object* v___x_1086_; 
v_cc_1085_ = lean_ctor_get(v_self_1082_, 14);
lean_inc_ref(v_cc_1085_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_cc_1085_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lake_LeanInstall_leanCc_x3f(v_self_1087_);
lean_dec_ref(v_self_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_1089_, lean_object* v_self_1090_){
_start:
{
if (v_shared_1089_ == 0)
{
lean_object* v_ccLinkStaticFlags_1091_; 
v_ccLinkStaticFlags_1091_ = lean_ctor_get(v_self_1090_, 19);
lean_inc_ref(v_ccLinkStaticFlags_1091_);
return v_ccLinkStaticFlags_1091_;
}
else
{
lean_object* v_ccLinkSharedFlags_1092_; 
v_ccLinkSharedFlags_1092_ = lean_ctor_get(v_self_1090_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1092_);
return v_ccLinkSharedFlags_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_1093_, lean_object* v_self_1094_){
_start:
{
uint8_t v_shared_boxed_1095_; lean_object* v_res_1096_; 
v_shared_boxed_1095_ = lean_unbox(v_shared_1093_);
v_res_1096_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_1095_, v_self_1094_);
lean_dec_ref(v_self_1094_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = l_System_FilePath_exeExtension;
v___x_1099_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1100_ = l_System_FilePath_addExtension(v___x_1099_, v___x_1098_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_1101_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = l_Lake_defaultBuildDir;
v___x_1103_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1104_ = l_System_FilePath_join(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = l_Lake_defaultBinDir;
v___x_1106_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1107_ = l_System_FilePath_join(v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__2(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lake_defaultLeanLibDir;
v___x_1109_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1110_ = l_System_FilePath_join(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__4(void){
_start:
{
uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = 0;
v___x_1113_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1114_ = l_Lake_nameToSharedLib(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__5(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
v___x_1116_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1117_ = l_System_FilePath_join(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__6(void){
_start:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1118_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1119_ = 0;
v___x_1120_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1121_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__5, &l_Lake_instInhabitedLakeInstall_default___closed__5_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__5);
v___x_1122_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v___x_1118_);
lean_ctor_set(v___x_1122_, 3, v___x_1118_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*4, v___x_1119_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__7(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lake_lakeExe;
v___x_1124_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1125_ = l_System_FilePath_join(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__8(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1126_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__7, &l_Lake_instInhabitedLakeInstall_default___closed__7_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__7);
v___x_1127_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__6, &l_Lake_instInhabitedLakeInstall_default___closed__6_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__6);
v___x_1128_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1129_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1130_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1131_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
lean_ctor_set(v___x_1131_, 2, v___x_1129_);
lean_ctor_set(v___x_1131_, 3, v___x_1128_);
lean_ctor_set(v___x_1131_, 4, v___x_1127_);
lean_ctor_set(v___x_1131_, 5, v___x_1126_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__8, &l_Lake_instInhabitedLakeInstall_default___closed__8_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__8);
return v___x_1132_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_1139_){
_start:
{
lean_object* v_home_1140_; lean_object* v_srcDir_1141_; lean_object* v_binDir_1142_; lean_object* v_libDir_1143_; lean_object* v_sharedDynlib_1144_; lean_object* v_lake_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_home_1140_ = lean_ctor_get(v_x_1139_, 0);
lean_inc_ref(v_home_1140_);
v_srcDir_1141_ = lean_ctor_get(v_x_1139_, 1);
lean_inc_ref(v_srcDir_1141_);
v_binDir_1142_ = lean_ctor_get(v_x_1139_, 2);
lean_inc_ref(v_binDir_1142_);
v_libDir_1143_ = lean_ctor_get(v_x_1139_, 3);
lean_inc_ref(v_libDir_1143_);
v_sharedDynlib_1144_ = lean_ctor_get(v_x_1139_, 4);
lean_inc_ref(v_sharedDynlib_1144_);
v_lake_1145_ = lean_ctor_get(v_x_1139_, 5);
lean_inc_ref(v_lake_1145_);
lean_dec_ref(v_x_1139_);
v___x_1146_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_1147_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_1148_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_1151_ = l_String_quote(v_home_1140_);
v___x_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1150_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Repr_addAppParen(v___x_1153_, v___x_1149_);
v___x_1155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1148_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = 0;
v___x_1157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*1, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1147_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_1160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_box(1);
v___x_1162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_1164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1146_);
v___x_1166_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_1167_ = l_String_quote(v_srcDir_1141_);
v___x_1168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1150_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Repr_addAppParen(v___x_1169_, v___x_1149_);
v___x_1171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1166_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*1, v___x_1156_);
v___x_1173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1165_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___x_1159_);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v___x_1161_);
v___x_1176_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_1177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1146_);
v___x_1179_ = l_String_quote(v_binDir_1142_);
v___x_1180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1150_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Repr_addAppParen(v___x_1181_, v___x_1149_);
v___x_1183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1166_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*1, v___x_1156_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1178_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___x_1159_);
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1161_);
v___x_1188_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_1189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1146_);
v___x_1191_ = l_String_quote(v_libDir_1143_);
v___x_1192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1150_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Repr_addAppParen(v___x_1193_, v___x_1149_);
v___x_1195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1166_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*1, v___x_1156_);
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1190_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1159_);
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1161_);
v___x_1200_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1146_);
v___x_1203_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_1204_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_1144_);
v___x_1205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*1, v___x_1156_);
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1202_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1159_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1161_);
v___x_1210_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__2));
v___x_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1146_);
v___x_1213_ = l_String_quote(v_lake_1145_);
v___x_1214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1150_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Repr_addAppParen(v___x_1215_, v___x_1149_);
v___x_1217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1148_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1, v___x_1156_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1212_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1221_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1219_);
v___x_1223_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1220_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*1, v___x_1156_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_1227_, lean_object* v_prec_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_1230_, lean_object* v_prec_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lake_instReprLakeInstall_repr(v_x_1230_, v_prec_1231_);
lean_dec(v_prec_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_1235_){
_start:
{
lean_object* v_sharedDynlib_1236_; lean_object* v_path_1237_; 
v_sharedDynlib_1236_ = lean_ctor_get(v_self_1235_, 4);
v_path_1237_ = lean_ctor_get(v_sharedDynlib_1236_, 0);
lean_inc_ref(v_path_1237_);
return v_path_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lake_LakeInstall_sharedLib(v_self_1238_);
lean_dec_ref(v_self_1238_);
return v_res_1239_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__2(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = l_Lake_sharedLibExt;
v___x_1243_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1244_ = lean_string_append(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_1246_){
_start:
{
lean_object* v_sysroot_1247_; lean_object* v_srcDir_1248_; lean_object* v_leanLibDir_1249_; lean_object* v_binDir_1250_; lean_object* v_sharedDynlibs_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___y_1255_; uint8_t v___x_1263_; 
v_sysroot_1247_ = lean_ctor_get(v_lean_1246_, 0);
lean_inc_ref(v_sysroot_1247_);
v_srcDir_1248_ = lean_ctor_get(v_lean_1246_, 2);
lean_inc_ref(v_srcDir_1248_);
v_leanLibDir_1249_ = lean_ctor_get(v_lean_1246_, 3);
lean_inc_ref(v_leanLibDir_1249_);
v_binDir_1250_ = lean_ctor_get(v_lean_1246_, 6);
lean_inc_ref(v_binDir_1250_);
v_sharedDynlibs_1251_ = lean_ctor_get(v_lean_1246_, 11);
lean_inc_ref(v_sharedDynlibs_1251_);
lean_dec_ref(v_lean_1246_);
v___x_1252_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1253_ = l_System_FilePath_join(v_srcDir_1248_, v___x_1252_);
v___x_1263_ = l_System_Platform_isWindows;
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__2, &l_Lake_LakeInstall_ofLean___closed__2_once, _init_l_Lake_LakeInstall_ofLean___closed__2);
lean_inc_ref(v_leanLibDir_1249_);
v___x_1265_ = l_System_FilePath_join(v_leanLibDir_1249_, v___x_1264_);
v___y_1255_ = v___x_1265_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__3));
lean_inc_ref(v_binDir_1250_);
v___x_1267_ = l_System_FilePath_join(v_binDir_1250_, v___x_1266_);
v___y_1255_ = v___x_1267_;
goto v___jp_1254_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1256_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_1257_ = 0;
v___x_1258_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1259_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1259_, 0, v___y_1255_);
lean_ctor_set(v___x_1259_, 1, v___x_1256_);
lean_ctor_set(v___x_1259_, 2, v_sharedDynlibs_1251_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*4, v___x_1257_);
v___x_1260_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_1250_);
v___x_1261_ = l_System_FilePath_join(v_binDir_1250_, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1262_, 0, v_sysroot_1247_);
lean_ctor_set(v___x_1262_, 1, v___x_1253_);
lean_ctor_set(v___x_1262_, 2, v_binDir_1250_);
lean_ctor_set(v___x_1262_, 3, v_leanLibDir_1249_);
lean_ctor_set(v___x_1262_, 4, v___x_1259_);
lean_ctor_set(v___x_1262_, 5, v___x_1261_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_1272_ = lean_io_getenv(v___x_1271_);
if (lean_obj_tag(v___x_1272_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1300_; 
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1300_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1300_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___y_1280_; 
v___x_1277_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_1278_ = lean_io_getenv(v___x_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_1280_ = v___x_1298_;
goto v___jp_1279_;
}
else
{
lean_object* v_val_1299_; 
v_val_1299_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1278_, 1);
v___y_1280_ = v_val_1299_;
goto v___jp_1279_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_startInclusive_1285_; lean_object* v_endExclusive_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_string_utf8_byte_size(v___y_1280_);
lean_inc_ref(v___y_1280_);
v___x_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1283_, 0, v___y_1280_);
lean_ctor_set(v___x_1283_, 1, v___x_1281_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
v___x_1284_ = l_String_Slice_trimAscii(v___x_1283_);
v_startInclusive_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_startInclusive_1285_);
v_endExclusive_1286_ = lean_ctor_get(v___x_1284_, 2);
lean_inc(v_endExclusive_1286_);
lean_dec_ref(v___x_1284_);
v___x_1287_ = lean_nat_sub(v_endExclusive_1286_, v_startInclusive_1285_);
lean_dec(v_startInclusive_1285_);
lean_dec(v_endExclusive_1286_);
v___x_1288_ = lean_nat_dec_eq(v___x_1287_, v___x_1281_);
lean_dec(v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1289_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
lean_inc_n(v_val_1273_, 2);
v___x_1290_ = l_System_FilePath_join(v_val_1273_, v___x_1289_);
v___x_1291_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_1292_ = l_System_FilePath_join(v_val_1273_, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1293_, 0, v_val_1273_);
lean_ctor_set(v___x_1293_, 1, v___y_1280_);
lean_ctor_set(v___x_1293_, 2, v___x_1290_);
lean_ctor_set(v___x_1293_, 3, v___x_1292_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1293_);
v___x_1295_ = v___x_1275_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
lean_object* v___x_1297_; 
lean_dec_ref(v___y_1280_);
lean_del_object(v___x_1275_);
lean_dec(v_val_1273_);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
}
}
}
else
{
lean_object* v___x_1301_; 
lean_dec(v___x_1272_);
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lake_findElanInstall_x3f();
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1315_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1316_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1320_ = 1;
v___x_1321_ = 0;
v___x_1322_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1322_, 0, v___x_1315_);
lean_ctor_set(v___x_1322_, 1, v_lean_1313_);
lean_ctor_set(v___x_1322_, 2, v___x_1316_);
lean_ctor_set(v___x_1322_, 3, v___x_1317_);
lean_ctor_set(v___x_1322_, 4, v___x_1319_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*5, v___x_1320_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*5 + 1, v___x_1321_);
v___x_1323_ = l_IO_Process_output(v___x_1322_, v___x_1317_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1342_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1342_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1342_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
uint32_t v_exitCode_1328_; lean_object* v_stdout_1329_; uint32_t v___x_1330_; uint8_t v___x_1331_; 
v_exitCode_1328_ = lean_ctor_get_uint32(v_a_1324_, sizeof(void*)*2);
v_stdout_1329_ = lean_ctor_get(v_a_1324_, 0);
lean_inc_ref(v_stdout_1329_);
lean_dec(v_a_1324_);
v___x_1330_ = 0;
v___x_1331_ = lean_uint32_dec_eq(v_exitCode_1328_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v_stdout_1329_);
lean_del_object(v___x_1326_);
return v___x_1317_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_str_1335_; lean_object* v_startInclusive_1336_; lean_object* v_endExclusive_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1332_ = lean_string_utf8_byte_size(v_stdout_1329_);
v___x_1333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1333_, 0, v_stdout_1329_);
lean_ctor_set(v___x_1333_, 1, v___x_1318_);
lean_ctor_set(v___x_1333_, 2, v___x_1332_);
v___x_1334_ = l_String_Slice_trimAscii(v___x_1333_);
v_str_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc_ref(v_str_1335_);
v_startInclusive_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_startInclusive_1336_);
v_endExclusive_1337_ = lean_ctor_get(v___x_1334_, 2);
lean_inc(v_endExclusive_1337_);
lean_dec_ref(v___x_1334_);
v___x_1338_ = lean_string_utf8_extract_fast(v_str_1335_, v_startInclusive_1336_, v_endExclusive_1337_);
lean_dec(v_endExclusive_1337_);
lean_dec(v_startInclusive_1336_);
lean_dec_ref(v_str_1335_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1338_);
v___x_1340_ = v___x_1326_;
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
}
else
{
lean_dec_ref_known(v___x_1323_, 1);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lake_findLeanSysroot_x3f(v_lean_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1353_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1354_ = l_Lake_leanExe(v_sysroot_1351_);
v___x_1355_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1359_ = 1;
v___x_1360_ = 0;
v___x_1361_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1361_, 0, v___x_1353_);
lean_ctor_set(v___x_1361_, 1, v___x_1354_);
lean_ctor_set(v___x_1361_, 2, v___x_1355_);
lean_ctor_set(v___x_1361_, 3, v___x_1356_);
lean_ctor_set(v___x_1361_, 4, v___x_1358_);
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*5, v___x_1359_);
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*5 + 1, v___x_1360_);
v___x_1362_ = l_IO_Process_output(v___x_1361_, v___x_1356_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v_stdout_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_str_1368_; lean_object* v_startInclusive_1369_; lean_object* v_endExclusive_1370_; lean_object* v___x_1371_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v_stdout_1364_ = lean_ctor_get(v_a_1363_, 0);
lean_inc_ref(v_stdout_1364_);
lean_dec(v_a_1363_);
v___x_1365_ = lean_string_utf8_byte_size(v_stdout_1364_);
v___x_1366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1366_, 0, v_stdout_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1357_);
lean_ctor_set(v___x_1366_, 2, v___x_1365_);
v___x_1367_ = l_String_Slice_trimAscii(v___x_1366_);
v_str_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc_ref(v_str_1368_);
v_startInclusive_1369_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_startInclusive_1369_);
v_endExclusive_1370_ = lean_ctor_get(v___x_1367_, 2);
lean_inc(v_endExclusive_1370_);
lean_dec_ref(v___x_1367_);
v___x_1371_ = lean_string_utf8_extract_fast(v_str_1368_, v_startInclusive_1369_, v_endExclusive_1370_);
lean_dec(v_endExclusive_1370_);
lean_dec(v_startInclusive_1369_);
lean_dec_ref(v_str_1368_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; 
lean_dec_ref_known(v___x_1362_, 1);
v___x_1372_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1381_ = lean_io_getenv(v___x_1380_);
if (lean_obj_tag(v___x_1381_) == 1)
{
lean_object* v_val_1382_; 
lean_dec_ref(v_sysroot_1378_);
v_val_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v___x_1381_, 1);
return v_val_1382_;
}
else
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
lean_dec(v___x_1381_);
v___x_1383_ = l_Lake_leanArExe(v_sysroot_1378_);
v___x_1384_ = l_System_FilePath_pathExists(v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v___x_1383_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1386_ = lean_io_getenv(v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 1)
{
lean_object* v_val_1387_; 
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_val_1387_);
lean_dec_ref_known(v___x_1386_, 1);
return v_val_1387_;
}
else
{
lean_object* v___x_1388_; 
lean_dec(v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
return v___x_1388_;
}
}
else
{
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1392_, lean_object* v_i_1393_, lean_object* v_cc_1394_){
_start:
{
lean_object* v_sysroot_1395_; lean_object* v_githash_1396_; lean_object* v_srcDir_1397_; lean_object* v_leanLibDir_1398_; lean_object* v_includeDir_1399_; lean_object* v_systemLibDir_1400_; lean_object* v_binDir_1401_; lean_object* v_lean_1402_; lean_object* v_leanir_1403_; lean_object* v_leanc_1404_; lean_object* v_leantar_1405_; lean_object* v_sharedDynlibs_1406_; lean_object* v_sharedDynlib_1407_; lean_object* v_ar_1408_; lean_object* v_cFlags_1409_; lean_object* v_linkStaticFlags_1410_; lean_object* v_linkSharedFlags_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1424_; 
v_sysroot_1395_ = lean_ctor_get(v_i_1393_, 0);
v_githash_1396_ = lean_ctor_get(v_i_1393_, 1);
v_srcDir_1397_ = lean_ctor_get(v_i_1393_, 2);
v_leanLibDir_1398_ = lean_ctor_get(v_i_1393_, 3);
v_includeDir_1399_ = lean_ctor_get(v_i_1393_, 4);
v_systemLibDir_1400_ = lean_ctor_get(v_i_1393_, 5);
v_binDir_1401_ = lean_ctor_get(v_i_1393_, 6);
v_lean_1402_ = lean_ctor_get(v_i_1393_, 7);
v_leanir_1403_ = lean_ctor_get(v_i_1393_, 8);
v_leanc_1404_ = lean_ctor_get(v_i_1393_, 9);
v_leantar_1405_ = lean_ctor_get(v_i_1393_, 10);
v_sharedDynlibs_1406_ = lean_ctor_get(v_i_1393_, 11);
v_sharedDynlib_1407_ = lean_ctor_get(v_i_1393_, 12);
v_ar_1408_ = lean_ctor_get(v_i_1393_, 13);
v_cFlags_1409_ = lean_ctor_get(v_i_1393_, 15);
v_linkStaticFlags_1410_ = lean_ctor_get(v_i_1393_, 16);
v_linkSharedFlags_1411_ = lean_ctor_get(v_i_1393_, 17);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_i_1393_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1425_ = lean_ctor_get(v_i_1393_, 20);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_i_1393_, 19);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_i_1393_, 18);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_i_1393_, 14);
lean_dec(v_unused_1428_);
v___x_1413_ = v_i_1393_;
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_linkSharedFlags_1411_);
lean_inc(v_linkStaticFlags_1410_);
lean_inc(v_cFlags_1409_);
lean_inc(v_ar_1408_);
lean_inc(v_sharedDynlib_1407_);
lean_inc(v_sharedDynlibs_1406_);
lean_inc(v_leantar_1405_);
lean_inc(v_leanc_1404_);
lean_inc(v_leanir_1403_);
lean_inc(v_lean_1402_);
lean_inc(v_binDir_1401_);
lean_inc(v_systemLibDir_1400_);
lean_inc(v_includeDir_1399_);
lean_inc(v_leanLibDir_1398_);
lean_inc(v_srcDir_1397_);
lean_inc(v_githash_1396_);
lean_inc(v_sysroot_1395_);
lean_dec(v_i_1393_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_ccLinkFlags_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v_ccLinkFlags_1415_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1392_);
v___x_1416_ = 0;
v___x_1417_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1392_);
lean_inc_ref(v_cFlags_1409_);
v___x_1418_ = l_Array_append___redArg(v_cFlags_1409_, v___x_1417_);
lean_dec_ref(v___x_1417_);
lean_inc_ref(v_ccLinkFlags_1415_);
v___x_1419_ = l_Array_append___redArg(v_ccLinkFlags_1415_, v_linkStaticFlags_1410_);
v___x_1420_ = l_Array_append___redArg(v_ccLinkFlags_1415_, v_linkSharedFlags_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 20, v___x_1420_);
lean_ctor_set(v___x_1413_, 19, v___x_1419_);
lean_ctor_set(v___x_1413_, 18, v___x_1418_);
lean_ctor_set(v___x_1413_, 14, v_cc_1394_);
v___x_1422_ = v___x_1413_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_sysroot_1395_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_githash_1396_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_srcDir_1397_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_leanLibDir_1398_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_includeDir_1399_);
lean_ctor_set(v_reuseFailAlloc_1423_, 5, v_systemLibDir_1400_);
lean_ctor_set(v_reuseFailAlloc_1423_, 6, v_binDir_1401_);
lean_ctor_set(v_reuseFailAlloc_1423_, 7, v_lean_1402_);
lean_ctor_set(v_reuseFailAlloc_1423_, 8, v_leanir_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 9, v_leanc_1404_);
lean_ctor_set(v_reuseFailAlloc_1423_, 10, v_leantar_1405_);
lean_ctor_set(v_reuseFailAlloc_1423_, 11, v_sharedDynlibs_1406_);
lean_ctor_set(v_reuseFailAlloc_1423_, 12, v_sharedDynlib_1407_);
lean_ctor_set(v_reuseFailAlloc_1423_, 13, v_ar_1408_);
lean_ctor_set(v_reuseFailAlloc_1423_, 14, v_cc_1394_);
lean_ctor_set(v_reuseFailAlloc_1423_, 15, v_cFlags_1409_);
lean_ctor_set(v_reuseFailAlloc_1423_, 16, v_linkStaticFlags_1410_);
lean_ctor_set(v_reuseFailAlloc_1423_, 17, v_linkSharedFlags_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 18, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1423_, 19, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1423_, 20, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*21, v___x_1416_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1429_, lean_object* v_i_1430_, lean_object* v_cc_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1429_, v_i_1430_, v_cc_1431_);
lean_dec_ref(v_sysroot_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1433_, lean_object* v_cc_1434_){
_start:
{
lean_object* v_sysroot_1435_; lean_object* v_githash_1436_; lean_object* v_srcDir_1437_; lean_object* v_leanLibDir_1438_; lean_object* v_includeDir_1439_; lean_object* v_systemLibDir_1440_; lean_object* v_binDir_1441_; lean_object* v_lean_1442_; lean_object* v_leanir_1443_; lean_object* v_leanc_1444_; lean_object* v_leantar_1445_; lean_object* v_sharedDynlibs_1446_; lean_object* v_sharedDynlib_1447_; lean_object* v_ar_1448_; uint8_t v_customCc_1449_; lean_object* v_cFlags_1450_; lean_object* v_linkStaticFlags_1451_; lean_object* v_linkSharedFlags_1452_; lean_object* v_ccFlags_1453_; lean_object* v_ccLinkStaticFlags_1454_; lean_object* v_ccLinkSharedFlags_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_sysroot_1435_ = lean_ctor_get(v_i_1433_, 0);
v_githash_1436_ = lean_ctor_get(v_i_1433_, 1);
v_srcDir_1437_ = lean_ctor_get(v_i_1433_, 2);
v_leanLibDir_1438_ = lean_ctor_get(v_i_1433_, 3);
v_includeDir_1439_ = lean_ctor_get(v_i_1433_, 4);
v_systemLibDir_1440_ = lean_ctor_get(v_i_1433_, 5);
v_binDir_1441_ = lean_ctor_get(v_i_1433_, 6);
v_lean_1442_ = lean_ctor_get(v_i_1433_, 7);
v_leanir_1443_ = lean_ctor_get(v_i_1433_, 8);
v_leanc_1444_ = lean_ctor_get(v_i_1433_, 9);
v_leantar_1445_ = lean_ctor_get(v_i_1433_, 10);
v_sharedDynlibs_1446_ = lean_ctor_get(v_i_1433_, 11);
v_sharedDynlib_1447_ = lean_ctor_get(v_i_1433_, 12);
v_ar_1448_ = lean_ctor_get(v_i_1433_, 13);
v_customCc_1449_ = lean_ctor_get_uint8(v_i_1433_, sizeof(void*)*21);
v_cFlags_1450_ = lean_ctor_get(v_i_1433_, 15);
v_linkStaticFlags_1451_ = lean_ctor_get(v_i_1433_, 16);
v_linkSharedFlags_1452_ = lean_ctor_get(v_i_1433_, 17);
v_ccFlags_1453_ = lean_ctor_get(v_i_1433_, 18);
v_ccLinkStaticFlags_1454_ = lean_ctor_get(v_i_1433_, 19);
v_ccLinkSharedFlags_1455_ = lean_ctor_get(v_i_1433_, 20);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_i_1433_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_i_1433_, 14);
lean_dec(v_unused_1463_);
v___x_1457_ = v_i_1433_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1455_);
lean_inc(v_ccLinkStaticFlags_1454_);
lean_inc(v_ccFlags_1453_);
lean_inc(v_linkSharedFlags_1452_);
lean_inc(v_linkStaticFlags_1451_);
lean_inc(v_cFlags_1450_);
lean_inc(v_ar_1448_);
lean_inc(v_sharedDynlib_1447_);
lean_inc(v_sharedDynlibs_1446_);
lean_inc(v_leantar_1445_);
lean_inc(v_leanc_1444_);
lean_inc(v_leanir_1443_);
lean_inc(v_lean_1442_);
lean_inc(v_binDir_1441_);
lean_inc(v_systemLibDir_1440_);
lean_inc(v_includeDir_1439_);
lean_inc(v_leanLibDir_1438_);
lean_inc(v_srcDir_1437_);
lean_inc(v_githash_1436_);
lean_inc(v_sysroot_1435_);
lean_dec(v_i_1433_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 14, v_cc_1434_);
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_sysroot_1435_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_githash_1436_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_srcDir_1437_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_leanLibDir_1438_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_includeDir_1439_);
lean_ctor_set(v_reuseFailAlloc_1461_, 5, v_systemLibDir_1440_);
lean_ctor_set(v_reuseFailAlloc_1461_, 6, v_binDir_1441_);
lean_ctor_set(v_reuseFailAlloc_1461_, 7, v_lean_1442_);
lean_ctor_set(v_reuseFailAlloc_1461_, 8, v_leanir_1443_);
lean_ctor_set(v_reuseFailAlloc_1461_, 9, v_leanc_1444_);
lean_ctor_set(v_reuseFailAlloc_1461_, 10, v_leantar_1445_);
lean_ctor_set(v_reuseFailAlloc_1461_, 11, v_sharedDynlibs_1446_);
lean_ctor_set(v_reuseFailAlloc_1461_, 12, v_sharedDynlib_1447_);
lean_ctor_set(v_reuseFailAlloc_1461_, 13, v_ar_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 14, v_cc_1434_);
lean_ctor_set(v_reuseFailAlloc_1461_, 15, v_cFlags_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 16, v_linkStaticFlags_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 17, v_linkSharedFlags_1452_);
lean_ctor_set(v_reuseFailAlloc_1461_, 18, v_ccFlags_1453_);
lean_ctor_set(v_reuseFailAlloc_1461_, 19, v_ccLinkStaticFlags_1454_);
lean_ctor_set(v_reuseFailAlloc_1461_, 20, v_ccLinkSharedFlags_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*21, v_customCc_1449_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1466_, lean_object* v_i_1467_){
_start:
{
lean_object* v_cc_1470_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1501_ = lean_io_getenv(v___x_1500_);
if (lean_obj_tag(v___x_1501_) == 1)
{
lean_object* v_val_1502_; 
lean_dec_ref(v_sysroot_1466_);
v_val_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v_cc_1470_ = v_val_1502_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
lean_dec(v___x_1501_);
lean_inc_ref(v_sysroot_1466_);
v___x_1503_ = l_Lake_leanCcExe(v_sysroot_1466_);
v___x_1504_ = l_System_FilePath_pathExists(v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v___x_1503_);
lean_dec_ref(v_sysroot_1466_);
v___x_1505_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1506_ = lean_io_getenv(v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 1)
{
lean_object* v_val_1507_; 
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v_cc_1470_ = v_val_1507_;
goto v___jp_1469_;
}
else
{
lean_object* v_sysroot_1508_; lean_object* v_githash_1509_; lean_object* v_srcDir_1510_; lean_object* v_leanLibDir_1511_; lean_object* v_includeDir_1512_; lean_object* v_systemLibDir_1513_; lean_object* v_binDir_1514_; lean_object* v_lean_1515_; lean_object* v_leanir_1516_; lean_object* v_leanc_1517_; lean_object* v_leantar_1518_; lean_object* v_sharedDynlibs_1519_; lean_object* v_sharedDynlib_1520_; lean_object* v_ar_1521_; uint8_t v_customCc_1522_; lean_object* v_cFlags_1523_; lean_object* v_linkStaticFlags_1524_; lean_object* v_linkSharedFlags_1525_; lean_object* v_ccFlags_1526_; lean_object* v_ccLinkStaticFlags_1527_; lean_object* v_ccLinkSharedFlags_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v___x_1506_);
v_sysroot_1508_ = lean_ctor_get(v_i_1467_, 0);
v_githash_1509_ = lean_ctor_get(v_i_1467_, 1);
v_srcDir_1510_ = lean_ctor_get(v_i_1467_, 2);
v_leanLibDir_1511_ = lean_ctor_get(v_i_1467_, 3);
v_includeDir_1512_ = lean_ctor_get(v_i_1467_, 4);
v_systemLibDir_1513_ = lean_ctor_get(v_i_1467_, 5);
v_binDir_1514_ = lean_ctor_get(v_i_1467_, 6);
v_lean_1515_ = lean_ctor_get(v_i_1467_, 7);
v_leanir_1516_ = lean_ctor_get(v_i_1467_, 8);
v_leanc_1517_ = lean_ctor_get(v_i_1467_, 9);
v_leantar_1518_ = lean_ctor_get(v_i_1467_, 10);
v_sharedDynlibs_1519_ = lean_ctor_get(v_i_1467_, 11);
v_sharedDynlib_1520_ = lean_ctor_get(v_i_1467_, 12);
v_ar_1521_ = lean_ctor_get(v_i_1467_, 13);
v_customCc_1522_ = lean_ctor_get_uint8(v_i_1467_, sizeof(void*)*21);
v_cFlags_1523_ = lean_ctor_get(v_i_1467_, 15);
v_linkStaticFlags_1524_ = lean_ctor_get(v_i_1467_, 16);
v_linkSharedFlags_1525_ = lean_ctor_get(v_i_1467_, 17);
v_ccFlags_1526_ = lean_ctor_get(v_i_1467_, 18);
v_ccLinkStaticFlags_1527_ = lean_ctor_get(v_i_1467_, 19);
v_ccLinkSharedFlags_1528_ = lean_ctor_get(v_i_1467_, 20);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_i_1467_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_i_1467_, 14);
lean_dec(v_unused_1537_);
v___x_1530_ = v_i_1467_;
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1528_);
lean_inc(v_ccLinkStaticFlags_1527_);
lean_inc(v_ccFlags_1526_);
lean_inc(v_linkSharedFlags_1525_);
lean_inc(v_linkStaticFlags_1524_);
lean_inc(v_cFlags_1523_);
lean_inc(v_ar_1521_);
lean_inc(v_sharedDynlib_1520_);
lean_inc(v_sharedDynlibs_1519_);
lean_inc(v_leantar_1518_);
lean_inc(v_leanc_1517_);
lean_inc(v_leanir_1516_);
lean_inc(v_lean_1515_);
lean_inc(v_binDir_1514_);
lean_inc(v_systemLibDir_1513_);
lean_inc(v_includeDir_1512_);
lean_inc(v_leanLibDir_1511_);
lean_inc(v_srcDir_1510_);
lean_inc(v_githash_1509_);
lean_inc(v_sysroot_1508_);
lean_dec(v_i_1467_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 14, v___x_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_sysroot_1508_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_githash_1509_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_srcDir_1510_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_leanLibDir_1511_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_includeDir_1512_);
lean_ctor_set(v_reuseFailAlloc_1535_, 5, v_systemLibDir_1513_);
lean_ctor_set(v_reuseFailAlloc_1535_, 6, v_binDir_1514_);
lean_ctor_set(v_reuseFailAlloc_1535_, 7, v_lean_1515_);
lean_ctor_set(v_reuseFailAlloc_1535_, 8, v_leanir_1516_);
lean_ctor_set(v_reuseFailAlloc_1535_, 9, v_leanc_1517_);
lean_ctor_set(v_reuseFailAlloc_1535_, 10, v_leantar_1518_);
lean_ctor_set(v_reuseFailAlloc_1535_, 11, v_sharedDynlibs_1519_);
lean_ctor_set(v_reuseFailAlloc_1535_, 12, v_sharedDynlib_1520_);
lean_ctor_set(v_reuseFailAlloc_1535_, 13, v_ar_1521_);
lean_ctor_set(v_reuseFailAlloc_1535_, 14, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 15, v_cFlags_1523_);
lean_ctor_set(v_reuseFailAlloc_1535_, 16, v_linkStaticFlags_1524_);
lean_ctor_set(v_reuseFailAlloc_1535_, 17, v_linkSharedFlags_1525_);
lean_ctor_set(v_reuseFailAlloc_1535_, 18, v_ccFlags_1526_);
lean_ctor_set(v_reuseFailAlloc_1535_, 19, v_ccLinkStaticFlags_1527_);
lean_ctor_set(v_reuseFailAlloc_1535_, 20, v_ccLinkSharedFlags_1528_);
lean_ctor_set_uint8(v_reuseFailAlloc_1535_, sizeof(void*)*21, v_customCc_1522_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v___x_1538_; 
v___x_1538_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1466_, v_i_1467_, v___x_1503_);
lean_dec_ref(v_sysroot_1466_);
return v___x_1538_;
}
}
v___jp_1469_:
{
lean_object* v_sysroot_1471_; lean_object* v_githash_1472_; lean_object* v_srcDir_1473_; lean_object* v_leanLibDir_1474_; lean_object* v_includeDir_1475_; lean_object* v_systemLibDir_1476_; lean_object* v_binDir_1477_; lean_object* v_lean_1478_; lean_object* v_leanir_1479_; lean_object* v_leanc_1480_; lean_object* v_leantar_1481_; lean_object* v_sharedDynlibs_1482_; lean_object* v_sharedDynlib_1483_; lean_object* v_ar_1484_; uint8_t v_customCc_1485_; lean_object* v_cFlags_1486_; lean_object* v_linkStaticFlags_1487_; lean_object* v_linkSharedFlags_1488_; lean_object* v_ccFlags_1489_; lean_object* v_ccLinkStaticFlags_1490_; lean_object* v_ccLinkSharedFlags_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
v_sysroot_1471_ = lean_ctor_get(v_i_1467_, 0);
v_githash_1472_ = lean_ctor_get(v_i_1467_, 1);
v_srcDir_1473_ = lean_ctor_get(v_i_1467_, 2);
v_leanLibDir_1474_ = lean_ctor_get(v_i_1467_, 3);
v_includeDir_1475_ = lean_ctor_get(v_i_1467_, 4);
v_systemLibDir_1476_ = lean_ctor_get(v_i_1467_, 5);
v_binDir_1477_ = lean_ctor_get(v_i_1467_, 6);
v_lean_1478_ = lean_ctor_get(v_i_1467_, 7);
v_leanir_1479_ = lean_ctor_get(v_i_1467_, 8);
v_leanc_1480_ = lean_ctor_get(v_i_1467_, 9);
v_leantar_1481_ = lean_ctor_get(v_i_1467_, 10);
v_sharedDynlibs_1482_ = lean_ctor_get(v_i_1467_, 11);
v_sharedDynlib_1483_ = lean_ctor_get(v_i_1467_, 12);
v_ar_1484_ = lean_ctor_get(v_i_1467_, 13);
v_customCc_1485_ = lean_ctor_get_uint8(v_i_1467_, sizeof(void*)*21);
v_cFlags_1486_ = lean_ctor_get(v_i_1467_, 15);
v_linkStaticFlags_1487_ = lean_ctor_get(v_i_1467_, 16);
v_linkSharedFlags_1488_ = lean_ctor_get(v_i_1467_, 17);
v_ccFlags_1489_ = lean_ctor_get(v_i_1467_, 18);
v_ccLinkStaticFlags_1490_ = lean_ctor_get(v_i_1467_, 19);
v_ccLinkSharedFlags_1491_ = lean_ctor_get(v_i_1467_, 20);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_i_1467_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v_i_1467_, 14);
lean_dec(v_unused_1499_);
v___x_1493_ = v_i_1467_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1491_);
lean_inc(v_ccLinkStaticFlags_1490_);
lean_inc(v_ccFlags_1489_);
lean_inc(v_linkSharedFlags_1488_);
lean_inc(v_linkStaticFlags_1487_);
lean_inc(v_cFlags_1486_);
lean_inc(v_ar_1484_);
lean_inc(v_sharedDynlib_1483_);
lean_inc(v_sharedDynlibs_1482_);
lean_inc(v_leantar_1481_);
lean_inc(v_leanc_1480_);
lean_inc(v_leanir_1479_);
lean_inc(v_lean_1478_);
lean_inc(v_binDir_1477_);
lean_inc(v_systemLibDir_1476_);
lean_inc(v_includeDir_1475_);
lean_inc(v_leanLibDir_1474_);
lean_inc(v_srcDir_1473_);
lean_inc(v_githash_1472_);
lean_inc(v_sysroot_1471_);
lean_dec(v_i_1467_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 14, v_cc_1470_);
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_sysroot_1471_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_githash_1472_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_srcDir_1473_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_leanLibDir_1474_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_includeDir_1475_);
lean_ctor_set(v_reuseFailAlloc_1497_, 5, v_systemLibDir_1476_);
lean_ctor_set(v_reuseFailAlloc_1497_, 6, v_binDir_1477_);
lean_ctor_set(v_reuseFailAlloc_1497_, 7, v_lean_1478_);
lean_ctor_set(v_reuseFailAlloc_1497_, 8, v_leanir_1479_);
lean_ctor_set(v_reuseFailAlloc_1497_, 9, v_leanc_1480_);
lean_ctor_set(v_reuseFailAlloc_1497_, 10, v_leantar_1481_);
lean_ctor_set(v_reuseFailAlloc_1497_, 11, v_sharedDynlibs_1482_);
lean_ctor_set(v_reuseFailAlloc_1497_, 12, v_sharedDynlib_1483_);
lean_ctor_set(v_reuseFailAlloc_1497_, 13, v_ar_1484_);
lean_ctor_set(v_reuseFailAlloc_1497_, 14, v_cc_1470_);
lean_ctor_set(v_reuseFailAlloc_1497_, 15, v_cFlags_1486_);
lean_ctor_set(v_reuseFailAlloc_1497_, 16, v_linkStaticFlags_1487_);
lean_ctor_set(v_reuseFailAlloc_1497_, 17, v_linkSharedFlags_1488_);
lean_ctor_set(v_reuseFailAlloc_1497_, 18, v_ccFlags_1489_);
lean_ctor_set(v_reuseFailAlloc_1497_, 19, v_ccLinkStaticFlags_1490_);
lean_ctor_set(v_reuseFailAlloc_1497_, 20, v_ccLinkSharedFlags_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*21, v_customCc_1485_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1539_, lean_object* v_i_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1539_, v_i_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1543_, uint8_t v_collocated_1544_){
_start:
{
lean_object* v_githash_1547_; 
if (v_collocated_1544_ == 0)
{
lean_object* v___x_1573_; 
lean_inc_ref(v_sysroot_1543_);
v___x_1573_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1543_);
v_githash_1547_ = v___x_1573_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_githash;
v_githash_1547_ = v___x_1574_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_inc_ref_n(v_sysroot_1543_, 12);
v___x_1548_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1543_);
v___x_1549_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1550_ = l_System_FilePath_join(v_sysroot_1543_, v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1552_ = l_System_FilePath_join(v___x_1550_, v___x_1551_);
v___x_1553_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1554_ = l_System_FilePath_join(v_sysroot_1543_, v___x_1553_);
lean_inc_ref(v___x_1554_);
v___x_1555_ = l_System_FilePath_join(v___x_1554_, v___x_1551_);
v___x_1556_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1557_ = l_System_FilePath_join(v_sysroot_1543_, v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1559_ = l_System_FilePath_join(v_sysroot_1543_, v___x_1558_);
v___x_1560_ = l_Lake_leanExe(v_sysroot_1543_);
v___x_1561_ = l_Lake_leanirExe(v_sysroot_1543_);
v___x_1562_ = l_Lake_leancExe(v_sysroot_1543_);
v___x_1563_ = l_Lake_leantarExe(v_sysroot_1543_);
v___x_1564_ = l_Lake_leanSharedDynlibs(v_sysroot_1543_);
v___x_1565_ = l_Lake_leanSharedDynlib(v_sysroot_1543_);
v___x_1566_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1567_ = 1;
v___x_1568_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1569_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1570_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_1571_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1571_, 0, v_sysroot_1543_);
lean_ctor_set(v___x_1571_, 1, v_githash_1547_);
lean_ctor_set(v___x_1571_, 2, v___x_1552_);
lean_ctor_set(v___x_1571_, 3, v___x_1555_);
lean_ctor_set(v___x_1571_, 4, v___x_1557_);
lean_ctor_set(v___x_1571_, 5, v___x_1554_);
lean_ctor_set(v___x_1571_, 6, v___x_1559_);
lean_ctor_set(v___x_1571_, 7, v___x_1560_);
lean_ctor_set(v___x_1571_, 8, v___x_1561_);
lean_ctor_set(v___x_1571_, 9, v___x_1562_);
lean_ctor_set(v___x_1571_, 10, v___x_1563_);
lean_ctor_set(v___x_1571_, 11, v___x_1564_);
lean_ctor_set(v___x_1571_, 12, v___x_1565_);
lean_ctor_set(v___x_1571_, 13, v___x_1548_);
lean_ctor_set(v___x_1571_, 14, v___x_1566_);
lean_ctor_set(v___x_1571_, 15, v___x_1568_);
lean_ctor_set(v___x_1571_, 16, v___x_1569_);
lean_ctor_set(v___x_1571_, 17, v___x_1570_);
lean_ctor_set(v___x_1571_, 18, v___x_1568_);
lean_ctor_set(v___x_1571_, 19, v___x_1569_);
lean_ctor_set(v___x_1571_, 20, v___x_1570_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*21, v___x_1567_);
v___x_1572_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1543_, v___x_1571_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1575_, lean_object* v_collocated_1576_, lean_object* v_a_1577_){
_start:
{
uint8_t v_collocated_boxed_1578_; lean_object* v_res_1579_; 
v_collocated_boxed_1578_ = lean_unbox(v_collocated_1576_);
v_res_1579_ = l_Lake_LeanInstall_get(v_sysroot_1575_, v_collocated_boxed_1578_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lake_findLeanSysroot_x3f(v_lean_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_box(0);
return v___x_1583_;
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1593_; 
v_val_1584_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1586_ = v___x_1582_;
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_val_1584_);
lean_dec(v___x_1582_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = 0;
v___x_1589_ = l_Lake_LeanInstall_get(v_val_1584_, v___x_1588_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_io_app_path();
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = l_System_FilePath_parent(v_a_1601_);
if (lean_obj_tag(v___x_1602_) == 1)
{
lean_object* v_val_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_val_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_n(v_val_1603_, 2);
lean_dec_ref_known(v___x_1602_, 1);
v___x_1604_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1605_ = l_System_FilePath_join(v_val_1603_, v___x_1604_);
v___x_1606_ = l_System_FilePath_exeExtension;
v___x_1607_ = l_System_FilePath_addExtension(v___x_1605_, v___x_1606_);
v___x_1608_ = l_System_FilePath_pathExists(v___x_1607_);
lean_dec_ref(v___x_1607_);
if (v___x_1608_ == 0)
{
lean_dec(v_val_1603_);
goto v___jp_1598_;
}
else
{
lean_object* v___x_1609_; 
v___x_1609_ = l_System_FilePath_parent(v_val_1603_);
return v___x_1609_;
}
}
else
{
lean_dec(v___x_1602_);
goto v___jp_1598_;
}
}
else
{
lean_dec_ref_known(v___x_1600_, 1);
goto v___jp_1598_;
}
v___jp_1598_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_box(0);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_System_FilePath_parent(v_lake_1612_);
if (lean_obj_tag(v___x_1613_) == 0)
{
return v___x_1613_;
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1615_; 
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = l_System_FilePath_parent(v_val_1614_);
if (lean_obj_tag(v___x_1615_) == 0)
{
return v___x_1615_;
}
else
{
lean_object* v_val_1616_; lean_object* v___x_1617_; 
v_val_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_System_FilePath_parent(v_val_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
return v___x_1617_;
}
else
{
lean_object* v_val_1618_; lean_object* v___x_1619_; 
v_val_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = l_System_FilePath_parent(v_val_1618_);
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1621_){
_start:
{
lean_object* v___x_1623_; 
lean_inc_ref(v_lake_1621_);
v___x_1623_ = l_Lake_lakeBuildHome_x3f(v_lake_1621_);
if (lean_obj_tag(v___x_1623_) == 1)
{
lean_object* v_val_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1648_; 
v_val_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1648_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_val_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1648_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_lake_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1628_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1624_, 2);
v___x_1629_ = l_System_FilePath_join(v_val_1624_, v___x_1628_);
v___x_1630_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1629_);
v___x_1631_ = l_System_FilePath_join(v___x_1629_, v___x_1630_);
v___x_1632_ = l_Lake_defaultLeanLibDir;
v___x_1633_ = l_System_FilePath_join(v___x_1629_, v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1635_ = 0;
v___x_1636_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref_n(v___x_1633_, 2);
v___x_1637_ = l_System_FilePath_join(v___x_1633_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1639_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1634_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
lean_ctor_set(v___x_1639_, 3, v___x_1638_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*4, v___x_1635_);
v_lake_1640_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1640_, 0, v_val_1624_);
lean_ctor_set(v_lake_1640_, 1, v_val_1624_);
lean_ctor_set(v_lake_1640_, 2, v___x_1631_);
lean_ctor_set(v_lake_1640_, 3, v___x_1633_);
lean_ctor_set(v_lake_1640_, 4, v___x_1639_);
lean_ctor_set(v_lake_1640_, 5, v_lake_1621_);
v___x_1641_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1642_ = l_System_FilePath_join(v___x_1633_, v___x_1641_);
v___x_1643_ = l_System_FilePath_pathExists(v___x_1642_);
lean_dec_ref(v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref_known(v_lake_1640_, 6);
lean_del_object(v___x_1626_);
v___x_1644_ = lean_box(0);
return v___x_1644_;
}
else
{
lean_object* v___x_1646_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v_lake_1640_);
v___x_1646_ = v___x_1626_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_lake_1640_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v___x_1649_; 
lean_dec(v___x_1623_);
lean_dec_ref(v_lake_1621_);
v___x_1649_ = lean_box(0);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lake_getLakeInstall_x3f(v_lake_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1657_ = lean_io_getenv(v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 1)
{
lean_object* v_val_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
v_val_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_val_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = 0;
v___x_1663_ = l_Lake_LeanInstall_get(v_val_1658_, v___x_1662_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_lean_1671_; 
lean_dec(v___x_1657_);
v___x_1668_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1669_ = lean_io_getenv(v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v_startInclusive_1689_; lean_object* v_endExclusive_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_val_1684_ = lean_ctor_get(v___x_1669_, 0);
lean_inc_n(v_val_1684_, 2);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_string_utf8_byte_size(v_val_1684_);
v___x_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1687_, 0, v_val_1684_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
lean_ctor_set(v___x_1687_, 2, v___x_1686_);
v___x_1688_ = l_String_Slice_trimAscii(v___x_1687_);
v_startInclusive_1689_ = lean_ctor_get(v___x_1688_, 1);
lean_inc(v_startInclusive_1689_);
v_endExclusive_1690_ = lean_ctor_get(v___x_1688_, 2);
lean_inc(v_endExclusive_1690_);
lean_dec_ref(v___x_1688_);
v___x_1691_ = lean_nat_sub(v_endExclusive_1690_, v_startInclusive_1689_);
lean_dec(v_startInclusive_1689_);
lean_dec(v_endExclusive_1690_);
v___x_1692_ = lean_nat_dec_eq(v___x_1691_, v___x_1685_);
lean_dec(v___x_1691_);
if (v___x_1692_ == 0)
{
v_lean_1671_ = v_val_1684_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1693_; 
lean_dec(v_val_1684_);
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
}
else
{
lean_object* v___x_1694_; 
lean_dec(v___x_1669_);
v___x_1694_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v_lean_1671_ = v___x_1694_;
goto v___jp_1670_;
}
v___jp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lake_findLeanSysroot_x3f(v_lean_1671_);
if (lean_obj_tag(v___x_1672_) == 1)
{
lean_object* v_val_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v_val_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_val_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1677_ = 0;
v___x_1678_ = l_Lake_LeanInstall_get(v_val_1673_, v___x_1677_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v___x_1683_; 
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lake_findLeanInstall_x3f();
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_io_app_path();
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = l_Lake_getLakeInstall_x3f(v_a_1727_);
if (lean_obj_tag(v___x_1728_) == 1)
{
return v___x_1728_;
}
else
{
lean_dec(v___x_1728_);
goto v___jp_1699_;
}
}
else
{
lean_dec_ref_known(v___x_1726_, 1);
goto v___jp_1699_;
}
v___jp_1699_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1701_ = lean_io_getenv(v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 1)
{
lean_object* v_val_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1724_; 
v_val_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1724_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_val_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1724_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1706_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1702_, 2);
v___x_1707_ = l_System_FilePath_join(v_val_1702_, v___x_1706_);
v___x_1708_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1707_);
v___x_1709_ = l_System_FilePath_join(v___x_1707_, v___x_1708_);
v___x_1710_ = l_Lake_defaultLeanLibDir;
v___x_1711_ = l_System_FilePath_join(v___x_1707_, v___x_1710_);
v___x_1712_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1713_ = 0;
v___x_1714_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref(v___x_1711_);
v___x_1715_ = l_System_FilePath_join(v___x_1711_, v___x_1714_);
v___x_1716_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1717_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1712_);
lean_ctor_set(v___x_1717_, 2, v___x_1716_);
lean_ctor_set(v___x_1717_, 3, v___x_1716_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*4, v___x_1713_);
v___x_1718_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1709_);
v___x_1719_ = l_System_FilePath_join(v___x_1709_, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1720_, 0, v_val_1702_);
lean_ctor_set(v___x_1720_, 1, v_val_1702_);
lean_ctor_set(v___x_1720_, 2, v___x_1709_);
lean_ctor_set(v___x_1720_, 3, v___x_1711_);
lean_ctor_set(v___x_1720_, 4, v___x_1717_);
lean_ctor_set(v___x_1720_, 5, v___x_1719_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1720_);
v___x_1722_ = v___x_1704_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v___x_1725_; 
lean_dec(v___x_1701_);
v___x_1725_ = lean_box(0);
return v___x_1725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lake_findLakeInstall_x3f();
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l_Lake_findElanInstall_x3f();
v___x_1734_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1734_) == 1)
{
lean_object* v_val_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1792_; 
v_val_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1792_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_val_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1792_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1740_ = lean_io_getenv(v___x_1739_);
if (lean_obj_tag(v___x_1740_) == 0)
{
goto v___jp_1741_;
}
else
{
lean_object* v_val_1751_; lean_object* v___x_1752_; 
v_val_1751_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1752_ = l_Lake_envToBool_x3f(v_val_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
goto v___jp_1741_;
}
else
{
lean_object* v_val_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1791_; 
v_val_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1791_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_val_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1791_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_unbox(v_val_1753_);
if (v___x_1757_ == 0)
{
lean_del_object(v___x_1755_);
lean_dec(v_val_1753_);
goto v___jp_1741_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_del_object(v___x_1737_);
v___x_1758_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1759_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
lean_inc_n(v_val_1735_, 10);
v___x_1760_ = l_System_FilePath_join(v_val_1735_, v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1762_ = l_System_FilePath_join(v___x_1760_, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1764_ = l_System_FilePath_join(v_val_1735_, v___x_1763_);
lean_inc_ref(v___x_1764_);
v___x_1765_ = l_System_FilePath_join(v___x_1764_, v___x_1761_);
v___x_1766_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1767_ = l_System_FilePath_join(v_val_1735_, v___x_1766_);
v___x_1768_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1769_ = l_System_FilePath_join(v_val_1735_, v___x_1768_);
v___x_1770_ = l_Lake_leanExe(v_val_1735_);
v___x_1771_ = l_Lake_leanirExe(v_val_1735_);
v___x_1772_ = l_Lake_leancExe(v_val_1735_);
v___x_1773_ = l_Lake_leantarExe(v_val_1735_);
v___x_1774_ = l_Lake_leanSharedDynlibs(v_val_1735_);
v___x_1775_ = l_Lake_leanSharedDynlib(v_val_1735_);
v___x_1776_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_1777_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1778_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1779_ = lean_unbox(v_val_1753_);
v___x_1780_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1779_);
v___x_1781_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
lean_inc_ref(v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1782_, 0, v_val_1735_);
lean_ctor_set(v___x_1782_, 1, v___x_1758_);
lean_ctor_set(v___x_1782_, 2, v___x_1762_);
lean_ctor_set(v___x_1782_, 3, v___x_1765_);
lean_ctor_set(v___x_1782_, 4, v___x_1767_);
lean_ctor_set(v___x_1782_, 5, v___x_1764_);
lean_ctor_set(v___x_1782_, 6, v___x_1769_);
lean_ctor_set(v___x_1782_, 7, v___x_1770_);
lean_ctor_set(v___x_1782_, 8, v___x_1771_);
lean_ctor_set(v___x_1782_, 9, v___x_1772_);
lean_ctor_set(v___x_1782_, 10, v___x_1773_);
lean_ctor_set(v___x_1782_, 11, v___x_1774_);
lean_ctor_set(v___x_1782_, 12, v___x_1775_);
lean_ctor_set(v___x_1782_, 13, v___x_1776_);
lean_ctor_set(v___x_1782_, 14, v___x_1777_);
lean_ctor_set(v___x_1782_, 15, v___x_1778_);
lean_ctor_set(v___x_1782_, 16, v___x_1780_);
lean_ctor_set(v___x_1782_, 17, v___x_1781_);
lean_ctor_set(v___x_1782_, 18, v___x_1778_);
lean_ctor_set(v___x_1782_, 19, v___x_1780_);
lean_ctor_set(v___x_1782_, 20, v___x_1781_);
v___x_1783_ = lean_unbox(v_val_1753_);
lean_dec(v_val_1753_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*21, v___x_1783_);
v___x_1784_ = l_Lake_findLeanInstall_x3f();
v___x_1785_ = l_Lake_LakeInstall_ofLean(v___x_1782_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1785_);
v___x_1787_ = v___x_1755_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1784_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1733_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
return v___x_1789_;
}
}
}
}
}
v___jp_1741_:
{
uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1742_ = 1;
v___x_1743_ = l_Lake_LeanInstall_get(v_val_1735_, v___x_1742_);
lean_inc_ref(v___x_1743_);
v___x_1744_ = l_Lake_LakeInstall_ofLean(v___x_1743_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1743_);
v___x_1746_ = v___x_1737_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1743_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1744_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1733_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
return v___x_1749_;
}
}
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1734_);
v___x_1793_ = l_Lake_findLeanInstall_x3f();
v___x_1794_ = l_Lake_findLakeInstall_x3f();
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1733_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lake_findInstall_x3f();
return v_res_1798_;
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
