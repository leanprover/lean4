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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
uint8_t l_List_elem___at___00Lake_envToBool_x3f_spec__1(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_List_elem___at___00Lake_envToBool_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v_a_1_, v_x_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v_a_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec_ref(v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(lean_object* v_s_13_, lean_object* v_p_14_){
_start:
{
uint32_t v___y_16_; lean_object* v___x_21_; uint8_t v_decide_22_; 
v___x_21_ = lean_string_utf8_byte_size(v_s_13_);
v_decide_22_ = lean_nat_dec_eq(v_p_14_, v___x_21_);
if (v_decide_22_ == 0)
{
uint32_t v___x_23_; uint32_t v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_string_utf8_get_fast(v_s_13_, v_p_14_);
v___x_24_ = 65;
v___x_25_ = lean_uint32_dec_le(v___x_24_, v___x_23_);
if (v___x_25_ == 0)
{
v___y_16_ = v___x_23_;
goto v___jp_15_;
}
else
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 90;
v___x_27_ = lean_uint32_dec_le(v___x_23_, v___x_26_);
if (v___x_27_ == 0)
{
v___y_16_ = v___x_23_;
goto v___jp_15_;
}
else
{
uint32_t v___x_28_; uint32_t v___x_29_; 
v___x_28_ = 32;
v___x_29_ = lean_uint32_add(v___x_23_, v___x_28_);
v___y_16_ = v___x_29_;
goto v___jp_15_;
}
}
}
else
{
lean_dec(v_p_14_);
return v_s_13_;
}
v___jp_15_:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_inc(v_p_14_);
v___x_17_ = lean_string_utf8_set(v_s_13_, v_p_14_, v___y_16_);
v___x_18_ = l_Char_utf8Size(v___y_16_);
v___x_19_ = lean_nat_add(v_p_14_, v___x_18_);
lean_dec(v___x_18_);
lean_dec(v_p_14_);
v_s_13_ = v___x_17_;
v_p_14_ = v___x_19_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* v_o_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_79_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__11));
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_78_, v___x_80_);
v___x_82_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_81_, v___x_79_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lake_envToBool_x3f___closed__23));
v___x_84_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_81_, v___x_83_);
lean_dec_ref(v___x_81_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(0);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_box(v___x_82_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec_ref(v___x_81_);
v___x_88_ = lean_box(v___x_82_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_93_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_94_ = l_System_FilePath_join(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_97_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_98_ = l_System_FilePath_join(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default___closed__5(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__4, &l_Lake_instInhabitedElanInstall_default___closed__4_once, _init_l_Lake_instInhabitedElanInstall_default___closed__4);
v___x_100_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_101_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
lean_ctor_set(v___x_102_, 2, v___x_100_);
lean_ctor_set(v___x_102_, 3, v___x_99_);
return v___x_102_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall_default(void){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__5, &l_Lake_instInhabitedElanInstall_default___closed__5_once, _init_l_Lake_instInhabitedElanInstall_default___closed__5);
return v___x_103_;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lake_instInhabitedElanInstall_default;
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_nat_to_int(v_a_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(8u);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(10u);
v___x_135_ = lean_nat_to_int(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(17u);
v___x_140_ = lean_nat_to_int(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__0));
v___x_143_ = lean_string_length(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lake_instReprElanInstall_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__21, &l_Lake_instReprElanInstall_repr___redArg___closed__21_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__21);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___redArg(lean_object* v_x_150_){
_start:
{
lean_object* v_home_151_; lean_object* v_elan_152_; lean_object* v_binDir_153_; lean_object* v_toolchainsDir_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_home_151_ = lean_ctor_get(v_x_150_, 0);
lean_inc_ref(v_home_151_);
v_elan_152_ = lean_ctor_get(v_x_150_, 1);
lean_inc_ref(v_elan_152_);
v_binDir_153_ = lean_ctor_get(v_x_150_, 2);
lean_inc_ref(v_binDir_153_);
v_toolchainsDir_154_ = lean_ctor_get(v_x_150_, 3);
lean_inc_ref(v_toolchainsDir_154_);
lean_dec_ref(v_x_150_);
v___x_155_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_156_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_157_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_160_ = l_String_quote(v_home_151_);
v___x_161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_159_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = l_Repr_addAppParen(v___x_162_, v___x_158_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_157_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_156_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = lean_box(1);
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__13));
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_155_);
v___x_175_ = l_String_quote(v_elan_152_);
v___x_176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_159_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = l_Repr_addAppParen(v___x_177_, v___x_158_);
v___x_179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_157_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*1, v___x_165_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_174_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_168_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_170_);
v___x_184_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_155_);
v___x_187_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_188_ = l_String_quote(v_binDir_153_);
v___x_189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_159_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v___x_158_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_187_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_165_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_186_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_168_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_170_);
v___x_197_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__18));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_155_);
v___x_200_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_201_ = l_String_quote(v_toolchainsDir_154_);
v___x_202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_159_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = l_Repr_addAppParen(v___x_203_, v___x_158_);
v___x_205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_200_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_165_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_199_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_209_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_207_);
v___x_211_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_208_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_165_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr(lean_object* v_x_215_, lean_object* v_prec_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lake_instReprElanInstall_repr___redArg(v_x_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall_repr___boxed(lean_object* v_x_218_, lean_object* v_prec_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lake_instReprElanInstall_repr(v_x_218_, v_prec_219_);
lean_dec(v_prec_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object* v_toolchain_225_, lean_object* v_acc_226_, lean_object* v_pos_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_string_utf8_at_end(v_toolchain_225_, v_pos_227_);
if (v___x_228_ == 0)
{
uint32_t v_c_229_; lean_object* v_pos_x27_230_; uint32_t v___x_231_; uint8_t v___x_232_; 
v_c_229_ = lean_string_utf8_get_fast(v_toolchain_225_, v_pos_227_);
v_pos_x27_230_ = lean_string_utf8_next_fast(v_toolchain_225_, v_pos_227_);
lean_dec(v_pos_227_);
v___x_231_ = 47;
v___x_232_ = lean_uint32_dec_eq(v_c_229_, v___x_231_);
if (v___x_232_ == 0)
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 58;
v___x_234_ = lean_uint32_dec_eq(v_c_229_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_string_push(v_acc_226_, v_c_229_);
v_acc_226_ = v___x_235_;
v_pos_227_ = v_pos_x27_230_;
goto _start;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0));
v___x_238_ = lean_string_append(v_acc_226_, v___x_237_);
v_acc_226_ = v___x_238_;
v_pos_227_ = v_pos_x27_230_;
goto _start;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1));
v___x_241_ = lean_string_append(v_acc_226_, v___x_240_);
v_acc_226_ = v___x_241_;
v_pos_227_ = v_pos_x27_230_;
goto _start;
}
}
else
{
lean_dec(v_pos_227_);
return v_acc_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(lean_object* v_toolchain_243_, lean_object* v_acc_244_, lean_object* v_pos_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_243_, v_acc_244_, v_pos_245_);
lean_dec_ref(v_toolchain_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir(lean_object* v_toolchain_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_247_, v___x_248_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_toolchain2Dir___boxed(lean_object* v_toolchain_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_toolchain2Dir(v_toolchain_251_);
lean_dec_ref(v_toolchain_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir(lean_object* v_toolchain_253_, lean_object* v_elan_254_){
_start:
{
lean_object* v_toolchainsDir_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_toolchainsDir_255_ = lean_ctor_get(v_elan_254_, 3);
lean_inc_ref(v_toolchainsDir_255_);
lean_dec_ref(v_elan_254_);
v___x_256_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_253_, v___x_256_, v___x_257_);
v___x_259_ = l_System_FilePath_join(v_toolchainsDir_255_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_ElanInstall_toolchainDir___boxed(lean_object* v_toolchain_260_, lean_object* v_elan_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_260_, v_elan_261_);
lean_dec_ref(v_toolchain_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* v_sysroot_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_266_ = l_System_FilePath_join(v_sysroot_264_, v___x_265_);
v___x_267_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_268_ = l_System_FilePath_join(v___x_266_, v___x_267_);
v___x_269_ = l_System_FilePath_exeExtension;
v___x_270_ = l_System_FilePath_addExtension(v___x_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanirExe(lean_object* v_sysroot_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_273_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_274_ = l_System_FilePath_join(v_sysroot_272_, v___x_273_);
v___x_275_ = ((lean_object*)(l_Lake_leanirExe___closed__0));
v___x_276_ = l_System_FilePath_join(v___x_274_, v___x_275_);
v___x_277_ = l_System_FilePath_exeExtension;
v___x_278_ = l_System_FilePath_addExtension(v___x_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* v_sysroot_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_282_ = l_System_FilePath_join(v_sysroot_280_, v___x_281_);
v___x_283_ = ((lean_object*)(l_Lake_leancExe___closed__0));
v___x_284_ = l_System_FilePath_join(v___x_282_, v___x_283_);
v___x_285_ = l_System_FilePath_exeExtension;
v___x_286_ = l_System_FilePath_addExtension(v___x_284_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_leantarExe(lean_object* v_sysroot_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_289_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_290_ = l_System_FilePath_join(v_sysroot_288_, v___x_289_);
v___x_291_ = ((lean_object*)(l_Lake_leantarExe___closed__0));
v___x_292_ = l_System_FilePath_join(v___x_290_, v___x_291_);
v___x_293_ = l_System_FilePath_exeExtension;
v___x_294_ = l_System_FilePath_addExtension(v___x_292_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* v_sysroot_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_298_ = l_System_FilePath_join(v_sysroot_296_, v___x_297_);
v___x_299_ = ((lean_object*)(l_Lake_leanArExe___closed__0));
v___x_300_ = l_System_FilePath_join(v___x_298_, v___x_299_);
v___x_301_ = l_System_FilePath_exeExtension;
v___x_302_ = l_System_FilePath_addExtension(v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* v_sysroot_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_305_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_306_ = l_System_FilePath_join(v_sysroot_304_, v___x_305_);
v___x_307_ = ((lean_object*)(l_Lake_leanCcExe___closed__0));
v___x_308_ = l_System_FilePath_join(v___x_306_, v___x_307_);
v___x_309_ = l_System_FilePath_exeExtension;
v___x_310_ = l_System_FilePath_addExtension(v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* v_sysroot_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = l_System_Platform_isWindows;
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_315_ = l_System_FilePath_join(v_sysroot_312_, v___x_314_);
v___x_316_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_317_ = l_System_FilePath_join(v___x_315_, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_319_ = l_System_FilePath_join(v_sysroot_312_, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib(lean_object* v_sysroot_323_, lean_object* v_name_324_, lean_object* v_deps_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_326_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_327_ = l_System_FilePath_join(v_sysroot_323_, v___x_326_);
v___x_328_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_329_ = lean_string_append(v___x_328_, v_name_324_);
v___x_330_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0));
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
v___x_332_ = l_System_FilePath_join(v___x_327_, v___x_331_);
v___x_333_ = 0;
v___x_334_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_335_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_335_, 0, v___x_332_);
lean_ctor_set(v___x_335_, 1, v_name_324_);
lean_ctor_set(v___x_335_, 2, v_deps_325_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*4, v___x_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg(lean_object* v_sysroot_337_, lean_object* v_name_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_339_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_340_ = l_System_FilePath_join(v_sysroot_337_, v___x_339_);
v___x_341_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_342_ = l_System_FilePath_join(v___x_340_, v___x_341_);
v___x_343_ = lean_string_append(v___x_339_, v_name_338_);
v___x_344_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
v___x_346_ = l_Lake_sharedLibExt;
v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
v___x_348_ = l_System_FilePath_join(v___x_342_, v___x_347_);
v___x_349_ = 0;
v___x_350_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_351_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_351_, 0, v___x_348_);
lean_ctor_set(v___x_351_, 1, v_name_338_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*4, v___x_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(lean_object* v_sysroot_352_, lean_object* v_name_353_, lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_355_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_356_ = l_System_FilePath_join(v_sysroot_352_, v___x_355_);
v___x_357_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_358_ = l_System_FilePath_join(v___x_356_, v___x_357_);
v___x_359_ = lean_string_append(v___x_355_, v_name_353_);
v___x_360_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
v___x_362_ = l_Lake_sharedLibExt;
v___x_363_ = lean_string_append(v___x_361_, v___x_362_);
v___x_364_ = l_System_FilePath_join(v___x_358_, v___x_363_);
v___x_365_ = 0;
v___x_366_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_367_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_367_, 0, v___x_364_);
lean_ctor_set(v___x_367_, 1, v_name_353_);
lean_ctor_set(v___x_367_, 2, v___x_366_);
lean_ctor_set(v___x_367_, 3, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*4, v___x_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___boxed(lean_object* v_sysroot_368_, lean_object* v_name_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(v_sysroot_368_, v_name_369_, v_x_370_);
lean_dec_ref(v_x_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs(lean_object* v_f_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_init_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_lean1_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_lean2_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_lean_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_377_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_378_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
lean_inc_ref_n(v_f_376_, 3);
v_init_379_ = lean_apply_2(v_f_376_, v___x_377_, v___x_378_);
v___x_380_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
lean_inc_ref_n(v_init_379_, 3);
v___x_383_ = lean_array_push(v___x_382_, v_init_379_);
v_lean1_384_ = lean_apply_2(v_f_376_, v___x_380_, v___x_383_);
v___x_385_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_386_ = lean_unsigned_to_nat(2u);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
lean_inc_ref_n(v_lean1_384_, 2);
v___x_388_ = lean_array_push(v___x_387_, v_lean1_384_);
v___x_389_ = lean_array_push(v___x_388_, v_init_379_);
v_lean2_390_ = lean_apply_2(v_f_376_, v___x_385_, v___x_389_);
v___x_391_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_392_ = lean_unsigned_to_nat(3u);
v___x_393_ = lean_mk_empty_array_with_capacity(v___x_392_);
lean_inc_ref(v_lean2_390_);
v___x_394_ = lean_array_push(v___x_393_, v_lean2_390_);
v___x_395_ = lean_array_push(v___x_394_, v_lean1_384_);
v___x_396_ = lean_array_push(v___x_395_, v_init_379_);
v_lean_397_ = lean_apply_2(v_f_376_, v___x_391_, v___x_396_);
v___x_398_ = lean_unsigned_to_nat(4u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_array_push(v___x_399_, v_lean_397_);
v___x_401_ = lean_array_push(v___x_400_, v_lean2_390_);
v___x_402_ = lean_array_push(v___x_401_, v_lean1_384_);
v___x_403_ = lean_array_push(v___x_402_, v_init_379_);
return v___x_403_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = l_Lake_sharedLibExt;
v___x_406_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__0));
v___x_407_ = lean_string_append(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__3(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = l_Lake_sharedLibExt;
v___x_410_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__2));
v___x_411_ = lean_string_append(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__5(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = l_Lake_sharedLibExt;
v___x_414_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__4));
v___x_415_ = lean_string_append(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__7(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = l_Lake_sharedLibExt;
v___x_418_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__6));
v___x_419_ = lean_string_append(v___x_418_, v___x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlibs(lean_object* v_sysroot_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_System_Platform_isWindows;
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_init_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_lean1_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_lean2_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_lean_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_426_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_427_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_428_ = l_System_FilePath_join(v_sysroot_424_, v___x_427_);
v___x_429_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_430_ = l_System_FilePath_join(v___x_428_, v___x_429_);
v___x_431_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__1, &l_Lake_leanSharedDynlibs___closed__1_once, _init_l_Lake_leanSharedDynlibs___closed__1);
lean_inc_ref_n(v___x_430_, 3);
v___x_432_ = l_System_FilePath_join(v___x_430_, v___x_431_);
v___x_433_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v_init_434_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_434_, 0, v___x_432_);
lean_ctor_set(v_init_434_, 1, v___x_426_);
lean_ctor_set(v_init_434_, 2, v___x_433_);
lean_ctor_set(v_init_434_, 3, v___x_433_);
lean_ctor_set_uint8(v_init_434_, sizeof(void*)*4, v___x_425_);
v___x_435_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_436_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__3, &l_Lake_leanSharedDynlibs___closed__3_once, _init_l_Lake_leanSharedDynlibs___closed__3);
v___x_437_ = l_System_FilePath_join(v___x_430_, v___x_436_);
v_lean1_438_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_438_, 0, v___x_437_);
lean_ctor_set(v_lean1_438_, 1, v___x_435_);
lean_ctor_set(v_lean1_438_, 2, v___x_433_);
lean_ctor_set(v_lean1_438_, 3, v___x_433_);
lean_ctor_set_uint8(v_lean1_438_, sizeof(void*)*4, v___x_425_);
v___x_439_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_440_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__5, &l_Lake_leanSharedDynlibs___closed__5_once, _init_l_Lake_leanSharedDynlibs___closed__5);
v___x_441_ = l_System_FilePath_join(v___x_430_, v___x_440_);
v_lean2_442_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_442_, 0, v___x_441_);
lean_ctor_set(v_lean2_442_, 1, v___x_439_);
lean_ctor_set(v_lean2_442_, 2, v___x_433_);
lean_ctor_set(v_lean2_442_, 3, v___x_433_);
lean_ctor_set_uint8(v_lean2_442_, sizeof(void*)*4, v___x_425_);
v___x_443_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_444_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__7, &l_Lake_leanSharedDynlibs___closed__7_once, _init_l_Lake_leanSharedDynlibs___closed__7);
v___x_445_ = l_System_FilePath_join(v___x_430_, v___x_444_);
v_lean_446_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_446_, 0, v___x_445_);
lean_ctor_set(v_lean_446_, 1, v___x_443_);
lean_ctor_set(v_lean_446_, 2, v___x_433_);
lean_ctor_set(v_lean_446_, 3, v___x_433_);
lean_ctor_set_uint8(v_lean_446_, sizeof(void*)*4, v___x_425_);
v___x_447_ = lean_unsigned_to_nat(4u);
v___x_448_ = lean_mk_empty_array_with_capacity(v___x_447_);
v___x_449_ = lean_array_push(v___x_448_, v_lean_446_);
v___x_450_ = lean_array_push(v___x_449_, v_lean2_442_);
v___x_451_ = lean_array_push(v___x_450_, v_lean1_438_);
v___x_452_ = lean_array_push(v___x_451_, v_init_434_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v_init_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_lean1_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_lean2_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_lean_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_453_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_454_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_455_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_456_ = l_System_FilePath_join(v_sysroot_424_, v___x_455_);
v___x_457_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__8));
lean_inc_ref_n(v___x_456_, 3);
v___x_458_ = l_System_FilePath_join(v___x_456_, v___x_457_);
v___x_459_ = 0;
v_init_460_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_460_, 0, v___x_458_);
lean_ctor_set(v_init_460_, 1, v___x_453_);
lean_ctor_set(v_init_460_, 2, v___x_454_);
lean_ctor_set(v_init_460_, 3, v___x_454_);
lean_ctor_set_uint8(v_init_460_, sizeof(void*)*4, v___x_459_);
v___x_461_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = lean_mk_empty_array_with_capacity(v___x_462_);
lean_inc_ref_n(v_init_460_, 3);
v___x_464_ = lean_array_push(v___x_463_, v_init_460_);
v___x_465_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__9));
v___x_466_ = l_System_FilePath_join(v___x_456_, v___x_465_);
v_lean1_467_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_467_, 0, v___x_466_);
lean_ctor_set(v_lean1_467_, 1, v___x_461_);
lean_ctor_set(v_lean1_467_, 2, v___x_464_);
lean_ctor_set(v_lean1_467_, 3, v___x_454_);
lean_ctor_set_uint8(v_lean1_467_, sizeof(void*)*4, v___x_459_);
v___x_468_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_469_ = lean_unsigned_to_nat(2u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
lean_inc_ref_n(v_lean1_467_, 2);
v___x_471_ = lean_array_push(v___x_470_, v_lean1_467_);
v___x_472_ = lean_array_push(v___x_471_, v_init_460_);
v___x_473_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__10));
v___x_474_ = l_System_FilePath_join(v___x_456_, v___x_473_);
v_lean2_475_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_475_, 0, v___x_474_);
lean_ctor_set(v_lean2_475_, 1, v___x_468_);
lean_ctor_set(v_lean2_475_, 2, v___x_472_);
lean_ctor_set(v_lean2_475_, 3, v___x_454_);
lean_ctor_set_uint8(v_lean2_475_, sizeof(void*)*4, v___x_459_);
v___x_476_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_477_ = lean_unsigned_to_nat(3u);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_477_);
lean_inc_ref(v_lean2_475_);
v___x_479_ = lean_array_push(v___x_478_, v_lean2_475_);
v___x_480_ = lean_array_push(v___x_479_, v_lean1_467_);
v___x_481_ = lean_array_push(v___x_480_, v_init_460_);
v___x_482_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__11));
v___x_483_ = l_System_FilePath_join(v___x_456_, v___x_482_);
v_lean_484_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_484_, 0, v___x_483_);
lean_ctor_set(v_lean_484_, 1, v___x_476_);
lean_ctor_set(v_lean_484_, 2, v___x_481_);
lean_ctor_set(v_lean_484_, 3, v___x_454_);
lean_ctor_set_uint8(v_lean_484_, sizeof(void*)*4, v___x_459_);
v___x_485_ = lean_unsigned_to_nat(4u);
v___x_486_ = lean_mk_empty_array_with_capacity(v___x_485_);
v___x_487_ = lean_array_push(v___x_486_, v_lean_484_);
v___x_488_ = lean_array_push(v___x_487_, v_lean2_475_);
v___x_489_ = lean_array_push(v___x_488_, v_lean1_467_);
v___x_490_ = lean_array_push(v___x_489_, v_init_460_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlib(lean_object* v_sysroot_491_){
_start:
{
lean_object* v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = l_Lake_leanSharedDynlibs(v_sysroot_491_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_array_uget(v___x_492_, v___x_493_);
lean_dec_ref(v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = l_Lake_sharedLibExt;
v___x_497_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_498_ = l_System_FilePath_addExtension(v___x_497_, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_499_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = l_Lake_sharedLibExt;
v___x_502_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_503_ = l_System_FilePath_addExtension(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_504_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_507_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_508_ = l_System_FilePath_join(v___x_507_, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_510_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
v___x_511_ = l_System_FilePath_join(v___x_510_, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_513_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_514_ = l_System_FilePath_join(v___x_513_, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_516_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_517_ = l_System_FilePath_join(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_520_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_521_ = l_System_FilePath_join(v___x_520_, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__7(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_523_ = l_Lake_leanExe(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__8(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_525_ = l_Lake_leanirExe(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__9(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_527_ = l_Lake_leancExe(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__10(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_529_ = l_Lake_leantarExe(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__11(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_531_ = l_Lake_leanSharedDynlibs(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__12(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_533_ = l_Lake_leanSharedDynlib(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__16(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_538_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_539_ = lean_array_push(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__17(void){
_start:
{
uint8_t v___x_540_; lean_object* v___x_541_; 
v___x_540_ = 1;
v___x_541_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__18(void){
_start:
{
uint8_t v___x_542_; lean_object* v___x_543_; 
v___x_542_ = 0;
v___x_543_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__19(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_544_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_545_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_546_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_547_ = 1;
v___x_548_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_549_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_550_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__12, &l_Lake_instInhabitedLeanInstall_default___closed__12_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__12);
v___x_551_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_552_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__10, &l_Lake_instInhabitedLeanInstall_default___closed__10_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__10);
v___x_553_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__9, &l_Lake_instInhabitedLeanInstall_default___closed__9_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__9);
v___x_554_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__8, &l_Lake_instInhabitedLeanInstall_default___closed__8_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__8);
v___x_555_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__7, &l_Lake_instInhabitedLeanInstall_default___closed__7_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__7);
v___x_556_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_557_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_558_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
v___x_559_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_560_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__2, &l_Lake_instInhabitedLeanInstall_default___closed__2_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__2);
v___x_561_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_562_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
lean_ctor_set(v___x_562_, 2, v___x_560_);
lean_ctor_set(v___x_562_, 3, v___x_559_);
lean_ctor_set(v___x_562_, 4, v___x_558_);
lean_ctor_set(v___x_562_, 5, v___x_557_);
lean_ctor_set(v___x_562_, 6, v___x_556_);
lean_ctor_set(v___x_562_, 7, v___x_555_);
lean_ctor_set(v___x_562_, 8, v___x_554_);
lean_ctor_set(v___x_562_, 9, v___x_553_);
lean_ctor_set(v___x_562_, 10, v___x_552_);
lean_ctor_set(v___x_562_, 11, v___x_551_);
lean_ctor_set(v___x_562_, 12, v___x_550_);
lean_ctor_set(v___x_562_, 13, v___x_549_);
lean_ctor_set(v___x_562_, 14, v___x_548_);
lean_ctor_set(v___x_562_, 15, v___x_546_);
lean_ctor_set(v___x_562_, 16, v___x_545_);
lean_ctor_set(v___x_562_, 17, v___x_544_);
lean_ctor_set(v___x_562_, 18, v___x_546_);
lean_ctor_set(v___x_562_, 19, v___x_545_);
lean_ctor_set(v___x_562_, 20, v___x_544_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*21, v___x_547_);
return v___x_562_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
return v___x_563_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_dec(v_x_565_);
return v_x_566_;
}
else
{
lean_object* v_head_568_; lean_object* v_tail_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_580_; 
v_head_568_ = lean_ctor_get(v_x_567_, 0);
v_tail_569_ = lean_ctor_get(v_x_567_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_580_ == 0)
{
v___x_571_ = v_x_567_;
v_isShared_572_ = v_isSharedCheck_580_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_tail_569_);
lean_inc(v_head_568_);
lean_dec(v_x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_580_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
lean_inc(v_x_565_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 5);
lean_ctor_set(v___x_571_, 1, v_x_565_);
lean_ctor_set(v___x_571_, 0, v_x_566_);
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_x_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_x_565_);
v___x_574_ = v_reuseFailAlloc_579_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l_String_quote(v_head_568_);
v___x_576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_574_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v_x_566_ = v___x_577_;
v_x_567_ = v_tail_569_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
lean_dec(v_x_581_);
return v_x_582_;
}
else
{
lean_object* v_head_584_; lean_object* v_tail_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_596_; 
v_head_584_ = lean_ctor_get(v_x_583_, 0);
v_tail_585_ = lean_ctor_get(v_x_583_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_596_ == 0)
{
v___x_587_ = v_x_583_;
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_tail_585_);
lean_inc(v_head_584_);
lean_dec(v_x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
lean_inc(v_x_581_);
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 5);
lean_ctor_set(v___x_587_, 1, v_x_581_);
lean_ctor_set(v___x_587_, 0, v_x_582_);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_x_582_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_x_581_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = l_String_quote(v_head_584_);
v___x_592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
v___x_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_590_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(v_x_581_, v___x_593_, v_tail_585_);
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(lean_object* v___y_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = l_String_quote(v___y_597_);
v___x_599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_602_; 
lean_dec(v_x_601_);
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v_tail_603_; 
v_tail_603_ = lean_ctor_get(v_x_600_, 1);
if (lean_obj_tag(v_tail_603_) == 0)
{
lean_object* v_head_604_; lean_object* v___x_605_; 
lean_dec(v_x_601_);
v_head_604_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_head_604_);
lean_dec_ref_known(v_x_600_, 2);
v___x_605_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_604_);
return v___x_605_;
}
else
{
lean_object* v_head_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_inc(v_tail_603_);
v_head_606_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_head_606_);
lean_dec_ref_known(v_x_600_, 2);
v___x_607_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_606_);
v___x_608_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(v_x_601_, v___x_607_, v_tail_603_);
return v___x_608_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0));
v___x_615_ = lean_string_length(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3);
v___x_617_ = lean_nat_to_int(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(lean_object* v_xs_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_array_get_size(v_xs_625_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_629_ = lean_array_to_list(v_xs_625_);
v___x_630_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_631_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(v___x_629_, v___x_630_);
v___x_632_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_633_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_631_);
v___x_635_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_632_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Std_Format_fill(v___x_637_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
lean_dec_ref(v_xs_625_);
v___x_639_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_dec(v_x_640_);
return v_x_641_;
}
else
{
lean_object* v_head_643_; lean_object* v_tail_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
v_head_643_ = lean_ctor_get(v_x_642_, 0);
v_tail_644_ = lean_ctor_get(v_x_642_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_654_ == 0)
{
v___x_646_ = v_x_642_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_tail_644_);
lean_inc(v_head_643_);
lean_dec(v_x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
lean_inc(v_x_640_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 5);
lean_ctor_set(v___x_646_, 1, v_x_640_);
lean_ctor_set(v___x_646_, 0, v_x_641_);
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_x_641_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_x_640_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_Lake_instReprDynlib_repr___redArg(v_head_643_);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v_x_641_ = v___x_651_;
v_x_642_ = v_tail_644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_dec(v_x_655_);
return v_x_656_;
}
else
{
lean_object* v_head_658_; lean_object* v_tail_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
v_head_658_ = lean_ctor_get(v_x_657_, 0);
v_tail_659_ = lean_ctor_get(v_x_657_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_669_ == 0)
{
v___x_661_ = v_x_657_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_tail_659_);
lean_inc(v_head_658_);
lean_dec(v_x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
lean_inc(v_x_655_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 5);
lean_ctor_set(v___x_661_, 1, v_x_655_);
lean_ctor_set(v___x_661_, 0, v_x_656_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_x_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_x_655_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = l_Lake_instReprDynlib_repr___redArg(v_head_658_);
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(v_x_655_, v___x_666_, v_tail_659_);
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v___x_672_; 
lean_dec(v_x_671_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
else
{
lean_object* v_tail_673_; 
v_tail_673_ = lean_ctor_get(v_x_670_, 1);
if (lean_obj_tag(v_tail_673_) == 0)
{
lean_object* v_head_674_; lean_object* v___x_675_; 
lean_dec(v_x_671_);
v_head_674_ = lean_ctor_get(v_x_670_, 0);
lean_inc(v_head_674_);
lean_dec_ref_known(v_x_670_, 2);
v___x_675_ = l_Lake_instReprDynlib_repr___redArg(v_head_674_);
return v___x_675_;
}
else
{
lean_object* v_head_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc(v_tail_673_);
v_head_676_ = lean_ctor_get(v_x_670_, 0);
lean_inc(v_head_676_);
lean_dec_ref_known(v_x_670_, 2);
v___x_677_ = l_Lake_instReprDynlib_repr___redArg(v_head_676_);
v___x_678_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_671_, v___x_677_, v_tail_673_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_array_get_size(v_xs_679_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_dec_eq(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_683_ = lean_array_to_list(v_xs_679_);
v___x_684_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_685_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_683_, v___x_684_);
v___x_686_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_687_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_685_);
v___x_689_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_686_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Std_Format_fill(v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; 
lean_dec_ref(v_xs_679_);
v___x_693_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_693_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(11u);
v___x_704_ = lean_nat_to_int(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(14u);
v___x_715_ = lean_nat_to_int(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(16u);
v___x_723_ = lean_nat_to_int(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(9u);
v___x_731_ = lean_nat_to_int(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(6u);
v___x_743_ = lean_nat_to_int(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(12u);
v___x_750_ = lean_nat_to_int(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(19u);
v___x_758_ = lean_nat_to_int(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(21u);
v___x_769_ = lean_nat_to_int(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_773_){
_start:
{
lean_object* v_sysroot_774_; lean_object* v_githash_775_; lean_object* v_srcDir_776_; lean_object* v_leanLibDir_777_; lean_object* v_includeDir_778_; lean_object* v_systemLibDir_779_; lean_object* v_binDir_780_; lean_object* v_lean_781_; lean_object* v_leanir_782_; lean_object* v_leanc_783_; lean_object* v_leantar_784_; lean_object* v_sharedDynlibs_785_; lean_object* v_sharedDynlib_786_; lean_object* v_ar_787_; lean_object* v_cc_788_; uint8_t v_customCc_789_; lean_object* v_cFlags_790_; lean_object* v_linkStaticFlags_791_; lean_object* v_linkSharedFlags_792_; lean_object* v_ccFlags_793_; lean_object* v_ccLinkStaticFlags_794_; lean_object* v_ccLinkSharedFlags_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_sysroot_774_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_sysroot_774_);
v_githash_775_ = lean_ctor_get(v_x_773_, 1);
lean_inc_ref(v_githash_775_);
v_srcDir_776_ = lean_ctor_get(v_x_773_, 2);
lean_inc_ref(v_srcDir_776_);
v_leanLibDir_777_ = lean_ctor_get(v_x_773_, 3);
lean_inc_ref(v_leanLibDir_777_);
v_includeDir_778_ = lean_ctor_get(v_x_773_, 4);
lean_inc_ref(v_includeDir_778_);
v_systemLibDir_779_ = lean_ctor_get(v_x_773_, 5);
lean_inc_ref(v_systemLibDir_779_);
v_binDir_780_ = lean_ctor_get(v_x_773_, 6);
lean_inc_ref(v_binDir_780_);
v_lean_781_ = lean_ctor_get(v_x_773_, 7);
lean_inc_ref(v_lean_781_);
v_leanir_782_ = lean_ctor_get(v_x_773_, 8);
lean_inc_ref(v_leanir_782_);
v_leanc_783_ = lean_ctor_get(v_x_773_, 9);
lean_inc_ref(v_leanc_783_);
v_leantar_784_ = lean_ctor_get(v_x_773_, 10);
lean_inc_ref(v_leantar_784_);
v_sharedDynlibs_785_ = lean_ctor_get(v_x_773_, 11);
lean_inc_ref(v_sharedDynlibs_785_);
v_sharedDynlib_786_ = lean_ctor_get(v_x_773_, 12);
lean_inc_ref(v_sharedDynlib_786_);
v_ar_787_ = lean_ctor_get(v_x_773_, 13);
lean_inc_ref(v_ar_787_);
v_cc_788_ = lean_ctor_get(v_x_773_, 14);
lean_inc_ref(v_cc_788_);
v_customCc_789_ = lean_ctor_get_uint8(v_x_773_, sizeof(void*)*21);
v_cFlags_790_ = lean_ctor_get(v_x_773_, 15);
lean_inc_ref(v_cFlags_790_);
v_linkStaticFlags_791_ = lean_ctor_get(v_x_773_, 16);
lean_inc_ref(v_linkStaticFlags_791_);
v_linkSharedFlags_792_ = lean_ctor_get(v_x_773_, 17);
lean_inc_ref(v_linkSharedFlags_792_);
v_ccFlags_793_ = lean_ctor_get(v_x_773_, 18);
lean_inc_ref(v_ccFlags_793_);
v_ccLinkStaticFlags_794_ = lean_ctor_get(v_x_773_, 19);
lean_inc_ref(v_ccLinkStaticFlags_794_);
v_ccLinkSharedFlags_795_ = lean_ctor_get(v_x_773_, 20);
lean_inc_ref(v_ccLinkSharedFlags_795_);
lean_dec_ref(v_x_773_);
v___x_796_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_797_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_798_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_801_ = l_String_quote(v_sysroot_774_);
v___x_802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Repr_addAppParen(v___x_803_, v___x_799_);
v___x_805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_798_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = 0;
v___x_807_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*1, v___x_806_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_797_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_box(1);
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_796_);
v___x_816_ = l_String_quote(v_githash_775_);
v___x_817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
v___x_818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_798_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*1, v___x_806_);
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_815_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_809_);
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_811_);
v___x_823_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v___x_796_);
v___x_826_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_827_ = l_String_quote(v_srcDir_776_);
v___x_828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_800_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Repr_addAppParen(v___x_829_, v___x_799_);
v___x_831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_826_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*1, v___x_806_);
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_825_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_809_);
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_811_);
v___x_836_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_796_);
v___x_839_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_840_ = l_String_quote(v_leanLibDir_777_);
v___x_841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_800_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Repr_addAppParen(v___x_842_, v___x_799_);
v___x_844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_839_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*1, v___x_806_);
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_838_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_809_);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_811_);
v___x_849_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_796_);
v___x_852_ = l_String_quote(v_includeDir_778_);
v___x_853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
v___x_854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_800_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Repr_addAppParen(v___x_854_, v___x_799_);
v___x_856_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_839_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*1, v___x_806_);
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_851_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_809_);
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_811_);
v___x_861_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_796_);
v___x_864_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_865_ = l_String_quote(v_systemLibDir_779_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_800_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Repr_addAppParen(v___x_867_, v___x_799_);
v___x_869_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_864_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_806_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_863_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_809_);
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_811_);
v___x_874_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_796_);
v___x_877_ = l_String_quote(v_binDir_780_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_800_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Repr_addAppParen(v___x_879_, v___x_799_);
v___x_881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_826_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*1, v___x_806_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_876_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_809_);
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_811_);
v___x_886_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_796_);
v___x_889_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_890_ = l_String_quote(v_lean_781_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_800_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Repr_addAppParen(v___x_892_, v___x_799_);
v___x_894_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_889_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_806_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_888_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_809_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_811_);
v___x_899_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_796_);
v___x_902_ = l_String_quote(v_leanir_782_);
v___x_903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_800_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Repr_addAppParen(v___x_904_, v___x_799_);
v___x_906_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_826_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*1, v___x_806_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_901_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_809_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_811_);
v___x_911_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_796_);
v___x_914_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_915_ = l_String_quote(v_leanc_783_);
v___x_916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_800_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Repr_addAppParen(v___x_917_, v___x_799_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_914_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_806_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_913_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_809_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_811_);
v___x_924_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_796_);
v___x_927_ = l_String_quote(v_leantar_784_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_800_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Repr_addAppParen(v___x_929_, v___x_799_);
v___x_931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_798_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*1, v___x_806_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_926_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_809_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_811_);
v___x_936_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_796_);
v___x_939_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_940_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_sharedDynlibs_785_);
v___x_941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_806_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_938_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_809_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_811_);
v___x_946_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_796_);
v___x_949_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_786_);
v___x_950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_864_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_806_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_948_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v___x_809_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_811_);
v___x_955_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_796_);
v___x_958_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__27, &l_Lake_instReprLeanInstall_repr___redArg___closed__27_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27);
v___x_959_ = l_String_quote(v_ar_787_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_800_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Repr_addAppParen(v___x_961_, v___x_799_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_958_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*1, v___x_806_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_957_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_809_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_811_);
v___x_968_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__28));
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_796_);
v___x_971_ = l_String_quote(v_cc_788_);
v___x_972_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_800_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Repr_addAppParen(v___x_973_, v___x_799_);
v___x_975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_958_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v___x_806_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_970_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_809_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_811_);
v___x_980_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_796_);
v___x_983_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__31, &l_Lake_instReprLeanInstall_repr___redArg___closed__31_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31);
v___x_984_ = l_Bool_repr___redArg(v_customCc_789_);
v___x_985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*1, v___x_806_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_982_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_809_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_811_);
v___x_990_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__33));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_796_);
v___x_993_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_cFlags_790_);
v___x_994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_826_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_806_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_992_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_809_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_811_);
v___x_999_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__35));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_796_);
v___x_1002_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__36, &l_Lake_instReprLeanInstall_repr___redArg___closed__36_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36);
v___x_1003_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkStaticFlags_791_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*1, v___x_806_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_809_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_811_);
v___x_1009_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__38));
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_796_);
v___x_1012_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkSharedFlags_792_);
v___x_1013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1002_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*1, v___x_806_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1011_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_809_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_811_);
v___x_1018_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__40));
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_796_);
v___x_1021_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccFlags_793_);
v___x_1022_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_798_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*1, v___x_806_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_809_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_811_);
v___x_1027_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__42));
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_796_);
v___x_1030_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__43, &l_Lake_instReprLeanInstall_repr___redArg___closed__43_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43);
v___x_1031_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkStaticFlags_794_);
v___x_1032_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*1, v___x_806_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1029_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_809_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_811_);
v___x_1037_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__45));
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_796_);
v___x_1040_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkSharedFlags_795_);
v___x_1041_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1030_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*1, v___x_806_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1039_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1045_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1043_);
v___x_1047_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1044_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*1, v___x_806_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_1051_, lean_object* v_prec_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_1054_, lean_object* v_prec_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lake_instReprLeanInstall_repr(v_x_1054_, v_prec_1055_);
lean_dec(v_prec_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib(lean_object* v_self_1059_){
_start:
{
lean_object* v_sharedDynlib_1060_; lean_object* v_path_1061_; 
v_sharedDynlib_1060_ = lean_ctor_get(v_self_1059_, 12);
v_path_1061_ = lean_ctor_get(v_sharedDynlib_1060_, 0);
lean_inc_ref(v_path_1061_);
return v_path_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib___boxed(lean_object* v_self_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lake_LeanInstall_sharedLib(v_self_1062_);
lean_dec_ref(v_self_1062_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_initSharedLib(lean_object* v_self_1064_){
_start:
{
lean_object* v_sysroot_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_sysroot_1065_ = lean_ctor_get(v_self_1064_, 0);
lean_inc_ref(v_sysroot_1065_);
lean_dec_ref(v_self_1064_);
v___x_1066_ = l_Lake_leanSharedLibDir(v_sysroot_1065_);
v___x_1067_ = l_Lake_initSharedLib;
v___x_1068_ = l_System_FilePath_join(v___x_1066_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = l_System_Platform_isWindows;
if (v___x_1070_ == 0)
{
lean_object* v_leanLibDir_1071_; lean_object* v_systemLibDir_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_leanLibDir_1071_ = lean_ctor_get(v_self_1069_, 3);
v_systemLibDir_1072_ = lean_ctor_get(v_self_1069_, 5);
v___x_1073_ = lean_box(0);
lean_inc_ref(v_systemLibDir_1072_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_systemLibDir_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
lean_inc_ref(v_leanLibDir_1071_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_leanLibDir_1071_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v_binDir_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_binDir_1076_ = lean_ctor_get(v_self_1069_, 6);
v___x_1077_ = lean_box(0);
lean_inc_ref(v_binDir_1076_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_binDir_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lake_LeanInstall_sharedLibPath(v_self_1079_);
lean_dec_ref(v_self_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_1081_){
_start:
{
uint8_t v_customCc_1082_; 
v_customCc_1082_ = lean_ctor_get_uint8(v_self_1081_, sizeof(void*)*21);
if (v_customCc_1082_ == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_box(0);
return v___x_1083_;
}
else
{
lean_object* v_cc_1084_; lean_object* v___x_1085_; 
v_cc_1084_ = lean_ctor_get(v_self_1081_, 14);
lean_inc_ref(v_cc_1084_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_cc_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lake_LeanInstall_leanCc_x3f(v_self_1086_);
lean_dec_ref(v_self_1086_);
return v_res_1087_;
}
}
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_1088_, lean_object* v_self_1089_){
_start:
{
if (v_shared_1088_ == 0)
{
lean_object* v_ccLinkStaticFlags_1090_; 
v_ccLinkStaticFlags_1090_ = lean_ctor_get(v_self_1089_, 19);
lean_inc_ref(v_ccLinkStaticFlags_1090_);
return v_ccLinkStaticFlags_1090_;
}
else
{
lean_object* v_ccLinkSharedFlags_1091_; 
v_ccLinkSharedFlags_1091_ = lean_ctor_get(v_self_1089_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1091_);
return v_ccLinkSharedFlags_1091_;
}
}
}
LEAN_EXPORT void l_Lake_LeanInstall_ccLinkFlags_0interp(lean_interpreter_value* stack)
{
uint8_t v_shared_1088_ = stack[0].m_num;
lean_object* v_self_1089_ = stack[1].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_1088_, v_self_1089_);
stack->m_obj
 = v_res_1092_;
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
lean_object* l_Lake_findElanInstall_x3f(){
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
LEAN_EXPORT void l_Lake_findElanInstall_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1302_;
v_res_1302_ = l_Lake_findElanInstall_x3f();
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lake_findElanInstall_x3f();
return v_res_1304_;
}
}
lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1316_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1317_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1321_ = 1;
v___x_1322_ = 0;
v___x_1323_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1323_, 0, v___x_1316_);
lean_ctor_set(v___x_1323_, 1, v_lean_1314_);
lean_ctor_set(v___x_1323_, 2, v___x_1317_);
lean_ctor_set(v___x_1323_, 3, v___x_1318_);
lean_ctor_set(v___x_1323_, 4, v___x_1320_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*5, v___x_1321_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*5 + 1, v___x_1322_);
v___x_1324_ = l_IO_Process_output(v___x_1323_, v___x_1318_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1343_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1343_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1343_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
uint32_t v_exitCode_1329_; lean_object* v_stdout_1330_; uint32_t v___x_1331_; uint8_t v___x_1332_; 
v_exitCode_1329_ = lean_ctor_get_uint32(v_a_1325_, sizeof(void*)*2);
v_stdout_1330_ = lean_ctor_get(v_a_1325_, 0);
lean_inc_ref(v_stdout_1330_);
lean_dec(v_a_1325_);
v___x_1331_ = 0;
v___x_1332_ = lean_uint32_dec_eq(v_exitCode_1329_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_stdout_1330_);
lean_del_object(v___x_1327_);
return v___x_1318_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_str_1336_; lean_object* v_startInclusive_1337_; lean_object* v_endExclusive_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1333_ = lean_string_utf8_byte_size(v_stdout_1330_);
v___x_1334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1334_, 0, v_stdout_1330_);
lean_ctor_set(v___x_1334_, 1, v___x_1319_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
v___x_1335_ = l_String_Slice_trimAscii(v___x_1334_);
v_str_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc_ref(v_str_1336_);
v_startInclusive_1337_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_startInclusive_1337_);
v_endExclusive_1338_ = lean_ctor_get(v___x_1335_, 2);
lean_inc(v_endExclusive_1338_);
lean_dec_ref(v___x_1335_);
v___x_1339_ = lean_string_utf8_extract_fast(v_str_1336_, v_startInclusive_1337_, v_endExclusive_1338_);
lean_dec(v_endExclusive_1338_);
lean_dec(v_startInclusive_1337_);
lean_dec_ref(v_str_1336_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
lean_ctor_set(v___x_1327_, 0, v___x_1339_);
v___x_1341_ = v___x_1327_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1324_, 1);
return v___x_1318_;
}
}
}
LEAN_EXPORT void l_Lake_findLeanSysroot_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lean_1314_ = stack[0].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l_Lake_findLeanSysroot_x3f(v_lean_1314_);
stack->m_obj
 = v_res_1344_;
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lake_findLeanSysroot_x3f(v_lean_1345_);
return v_res_1347_;
}
}
lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1355_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1356_ = l_Lake_leanExe(v_sysroot_1353_);
v___x_1357_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1361_ = 1;
v___x_1362_ = 0;
v___x_1363_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1363_, 0, v___x_1355_);
lean_ctor_set(v___x_1363_, 1, v___x_1356_);
lean_ctor_set(v___x_1363_, 2, v___x_1357_);
lean_ctor_set(v___x_1363_, 3, v___x_1358_);
lean_ctor_set(v___x_1363_, 4, v___x_1360_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*5, v___x_1361_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*5 + 1, v___x_1362_);
v___x_1364_ = l_IO_Process_output(v___x_1363_, v___x_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_stdout_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_str_1370_; lean_object* v_startInclusive_1371_; lean_object* v_endExclusive_1372_; lean_object* v___x_1373_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_stdout_1366_ = lean_ctor_get(v_a_1365_, 0);
lean_inc_ref(v_stdout_1366_);
lean_dec(v_a_1365_);
v___x_1367_ = lean_string_utf8_byte_size(v_stdout_1366_);
v___x_1368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1368_, 0, v_stdout_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1359_);
lean_ctor_set(v___x_1368_, 2, v___x_1367_);
v___x_1369_ = l_String_Slice_trimAscii(v___x_1368_);
v_str_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc_ref(v_str_1370_);
v_startInclusive_1371_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_startInclusive_1371_);
v_endExclusive_1372_ = lean_ctor_get(v___x_1369_, 2);
lean_inc(v_endExclusive_1372_);
lean_dec_ref(v___x_1369_);
v___x_1373_ = lean_string_utf8_extract_fast(v_str_1370_, v_startInclusive_1371_, v_endExclusive_1372_);
lean_dec(v_endExclusive_1372_);
lean_dec(v_startInclusive_1371_);
lean_dec_ref(v_str_1370_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1374_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1374_;
}
}
}
LEAN_EXPORT void l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash_0interp(lean_interpreter_value* stack)
{
lean_object* v_sysroot_1353_ = stack[0].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1353_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1376_);
return v_res_1378_;
}
}
lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1381_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1384_ = lean_io_getenv(v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 1)
{
lean_object* v_val_1385_; 
lean_dec_ref(v_sysroot_1381_);
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
return v_val_1385_;
}
else
{
lean_object* v___x_1386_; uint8_t v___x_1387_; 
lean_dec(v___x_1384_);
v___x_1386_ = l_Lake_leanArExe(v_sysroot_1381_);
v___x_1387_ = l_System_FilePath_pathExists(v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v___x_1386_);
v___x_1388_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1389_ = lean_io_getenv(v___x_1388_);
if (lean_obj_tag(v___x_1389_) == 1)
{
lean_object* v_val_1390_; 
v_val_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1389_, 1);
return v_val_1390_;
}
else
{
lean_object* v___x_1391_; 
lean_dec(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
return v___x_1391_;
}
}
else
{
return v___x_1386_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr_0interp(lean_interpreter_value* stack)
{
lean_object* v_sysroot_1381_ = stack[0].m_obj;
lean_object* v_res_1392_;
v_res_1392_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1381_);
stack->m_obj
 = v_res_1392_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1396_, lean_object* v_i_1397_, lean_object* v_cc_1398_){
_start:
{
lean_object* v_sysroot_1399_; lean_object* v_githash_1400_; lean_object* v_srcDir_1401_; lean_object* v_leanLibDir_1402_; lean_object* v_includeDir_1403_; lean_object* v_systemLibDir_1404_; lean_object* v_binDir_1405_; lean_object* v_lean_1406_; lean_object* v_leanir_1407_; lean_object* v_leanc_1408_; lean_object* v_leantar_1409_; lean_object* v_sharedDynlibs_1410_; lean_object* v_sharedDynlib_1411_; lean_object* v_ar_1412_; lean_object* v_cFlags_1413_; lean_object* v_linkStaticFlags_1414_; lean_object* v_linkSharedFlags_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1428_; 
v_sysroot_1399_ = lean_ctor_get(v_i_1397_, 0);
v_githash_1400_ = lean_ctor_get(v_i_1397_, 1);
v_srcDir_1401_ = lean_ctor_get(v_i_1397_, 2);
v_leanLibDir_1402_ = lean_ctor_get(v_i_1397_, 3);
v_includeDir_1403_ = lean_ctor_get(v_i_1397_, 4);
v_systemLibDir_1404_ = lean_ctor_get(v_i_1397_, 5);
v_binDir_1405_ = lean_ctor_get(v_i_1397_, 6);
v_lean_1406_ = lean_ctor_get(v_i_1397_, 7);
v_leanir_1407_ = lean_ctor_get(v_i_1397_, 8);
v_leanc_1408_ = lean_ctor_get(v_i_1397_, 9);
v_leantar_1409_ = lean_ctor_get(v_i_1397_, 10);
v_sharedDynlibs_1410_ = lean_ctor_get(v_i_1397_, 11);
v_sharedDynlib_1411_ = lean_ctor_get(v_i_1397_, 12);
v_ar_1412_ = lean_ctor_get(v_i_1397_, 13);
v_cFlags_1413_ = lean_ctor_get(v_i_1397_, 15);
v_linkStaticFlags_1414_ = lean_ctor_get(v_i_1397_, 16);
v_linkSharedFlags_1415_ = lean_ctor_get(v_i_1397_, 17);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_i_1397_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; 
v_unused_1429_ = lean_ctor_get(v_i_1397_, 20);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_i_1397_, 19);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_i_1397_, 18);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_i_1397_, 14);
lean_dec(v_unused_1432_);
v___x_1417_ = v_i_1397_;
v_isShared_1418_ = v_isSharedCheck_1428_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_linkSharedFlags_1415_);
lean_inc(v_linkStaticFlags_1414_);
lean_inc(v_cFlags_1413_);
lean_inc(v_ar_1412_);
lean_inc(v_sharedDynlib_1411_);
lean_inc(v_sharedDynlibs_1410_);
lean_inc(v_leantar_1409_);
lean_inc(v_leanc_1408_);
lean_inc(v_leanir_1407_);
lean_inc(v_lean_1406_);
lean_inc(v_binDir_1405_);
lean_inc(v_systemLibDir_1404_);
lean_inc(v_includeDir_1403_);
lean_inc(v_leanLibDir_1402_);
lean_inc(v_srcDir_1401_);
lean_inc(v_githash_1400_);
lean_inc(v_sysroot_1399_);
lean_dec(v_i_1397_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1428_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_ccLinkFlags_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v_ccLinkFlags_1419_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1396_);
v___x_1420_ = 0;
v___x_1421_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1396_);
lean_inc_ref(v_cFlags_1413_);
v___x_1422_ = l_Array_append___redArg(v_cFlags_1413_, v___x_1421_);
lean_dec_ref(v___x_1421_);
lean_inc_ref(v_ccLinkFlags_1419_);
v___x_1423_ = l_Array_append___redArg(v_ccLinkFlags_1419_, v_linkStaticFlags_1414_);
v___x_1424_ = l_Array_append___redArg(v_ccLinkFlags_1419_, v_linkSharedFlags_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 20, v___x_1424_);
lean_ctor_set(v___x_1417_, 19, v___x_1423_);
lean_ctor_set(v___x_1417_, 18, v___x_1422_);
lean_ctor_set(v___x_1417_, 14, v_cc_1398_);
v___x_1426_ = v___x_1417_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_sysroot_1399_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_githash_1400_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_srcDir_1401_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_leanLibDir_1402_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_includeDir_1403_);
lean_ctor_set(v_reuseFailAlloc_1427_, 5, v_systemLibDir_1404_);
lean_ctor_set(v_reuseFailAlloc_1427_, 6, v_binDir_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 7, v_lean_1406_);
lean_ctor_set(v_reuseFailAlloc_1427_, 8, v_leanir_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 9, v_leanc_1408_);
lean_ctor_set(v_reuseFailAlloc_1427_, 10, v_leantar_1409_);
lean_ctor_set(v_reuseFailAlloc_1427_, 11, v_sharedDynlibs_1410_);
lean_ctor_set(v_reuseFailAlloc_1427_, 12, v_sharedDynlib_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 13, v_ar_1412_);
lean_ctor_set(v_reuseFailAlloc_1427_, 14, v_cc_1398_);
lean_ctor_set(v_reuseFailAlloc_1427_, 15, v_cFlags_1413_);
lean_ctor_set(v_reuseFailAlloc_1427_, 16, v_linkStaticFlags_1414_);
lean_ctor_set(v_reuseFailAlloc_1427_, 17, v_linkSharedFlags_1415_);
lean_ctor_set(v_reuseFailAlloc_1427_, 18, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1427_, 19, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1427_, 20, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*21, v___x_1420_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1433_, lean_object* v_i_1434_, lean_object* v_cc_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1433_, v_i_1434_, v_cc_1435_);
lean_dec_ref(v_sysroot_1433_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1437_, lean_object* v_cc_1438_){
_start:
{
lean_object* v_sysroot_1439_; lean_object* v_githash_1440_; lean_object* v_srcDir_1441_; lean_object* v_leanLibDir_1442_; lean_object* v_includeDir_1443_; lean_object* v_systemLibDir_1444_; lean_object* v_binDir_1445_; lean_object* v_lean_1446_; lean_object* v_leanir_1447_; lean_object* v_leanc_1448_; lean_object* v_leantar_1449_; lean_object* v_sharedDynlibs_1450_; lean_object* v_sharedDynlib_1451_; lean_object* v_ar_1452_; uint8_t v_customCc_1453_; lean_object* v_cFlags_1454_; lean_object* v_linkStaticFlags_1455_; lean_object* v_linkSharedFlags_1456_; lean_object* v_ccFlags_1457_; lean_object* v_ccLinkStaticFlags_1458_; lean_object* v_ccLinkSharedFlags_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_sysroot_1439_ = lean_ctor_get(v_i_1437_, 0);
v_githash_1440_ = lean_ctor_get(v_i_1437_, 1);
v_srcDir_1441_ = lean_ctor_get(v_i_1437_, 2);
v_leanLibDir_1442_ = lean_ctor_get(v_i_1437_, 3);
v_includeDir_1443_ = lean_ctor_get(v_i_1437_, 4);
v_systemLibDir_1444_ = lean_ctor_get(v_i_1437_, 5);
v_binDir_1445_ = lean_ctor_get(v_i_1437_, 6);
v_lean_1446_ = lean_ctor_get(v_i_1437_, 7);
v_leanir_1447_ = lean_ctor_get(v_i_1437_, 8);
v_leanc_1448_ = lean_ctor_get(v_i_1437_, 9);
v_leantar_1449_ = lean_ctor_get(v_i_1437_, 10);
v_sharedDynlibs_1450_ = lean_ctor_get(v_i_1437_, 11);
v_sharedDynlib_1451_ = lean_ctor_get(v_i_1437_, 12);
v_ar_1452_ = lean_ctor_get(v_i_1437_, 13);
v_customCc_1453_ = lean_ctor_get_uint8(v_i_1437_, sizeof(void*)*21);
v_cFlags_1454_ = lean_ctor_get(v_i_1437_, 15);
v_linkStaticFlags_1455_ = lean_ctor_get(v_i_1437_, 16);
v_linkSharedFlags_1456_ = lean_ctor_get(v_i_1437_, 17);
v_ccFlags_1457_ = lean_ctor_get(v_i_1437_, 18);
v_ccLinkStaticFlags_1458_ = lean_ctor_get(v_i_1437_, 19);
v_ccLinkSharedFlags_1459_ = lean_ctor_get(v_i_1437_, 20);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_i_1437_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_i_1437_, 14);
lean_dec(v_unused_1467_);
v___x_1461_ = v_i_1437_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1459_);
lean_inc(v_ccLinkStaticFlags_1458_);
lean_inc(v_ccFlags_1457_);
lean_inc(v_linkSharedFlags_1456_);
lean_inc(v_linkStaticFlags_1455_);
lean_inc(v_cFlags_1454_);
lean_inc(v_ar_1452_);
lean_inc(v_sharedDynlib_1451_);
lean_inc(v_sharedDynlibs_1450_);
lean_inc(v_leantar_1449_);
lean_inc(v_leanc_1448_);
lean_inc(v_leanir_1447_);
lean_inc(v_lean_1446_);
lean_inc(v_binDir_1445_);
lean_inc(v_systemLibDir_1444_);
lean_inc(v_includeDir_1443_);
lean_inc(v_leanLibDir_1442_);
lean_inc(v_srcDir_1441_);
lean_inc(v_githash_1440_);
lean_inc(v_sysroot_1439_);
lean_dec(v_i_1437_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 14, v_cc_1438_);
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_sysroot_1439_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_githash_1440_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_srcDir_1441_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_leanLibDir_1442_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_includeDir_1443_);
lean_ctor_set(v_reuseFailAlloc_1465_, 5, v_systemLibDir_1444_);
lean_ctor_set(v_reuseFailAlloc_1465_, 6, v_binDir_1445_);
lean_ctor_set(v_reuseFailAlloc_1465_, 7, v_lean_1446_);
lean_ctor_set(v_reuseFailAlloc_1465_, 8, v_leanir_1447_);
lean_ctor_set(v_reuseFailAlloc_1465_, 9, v_leanc_1448_);
lean_ctor_set(v_reuseFailAlloc_1465_, 10, v_leantar_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 11, v_sharedDynlibs_1450_);
lean_ctor_set(v_reuseFailAlloc_1465_, 12, v_sharedDynlib_1451_);
lean_ctor_set(v_reuseFailAlloc_1465_, 13, v_ar_1452_);
lean_ctor_set(v_reuseFailAlloc_1465_, 14, v_cc_1438_);
lean_ctor_set(v_reuseFailAlloc_1465_, 15, v_cFlags_1454_);
lean_ctor_set(v_reuseFailAlloc_1465_, 16, v_linkStaticFlags_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 17, v_linkSharedFlags_1456_);
lean_ctor_set(v_reuseFailAlloc_1465_, 18, v_ccFlags_1457_);
lean_ctor_set(v_reuseFailAlloc_1465_, 19, v_ccLinkStaticFlags_1458_);
lean_ctor_set(v_reuseFailAlloc_1465_, 20, v_ccLinkSharedFlags_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*21, v_customCc_1453_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1470_, lean_object* v_i_1471_){
_start:
{
lean_object* v_cc_1474_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1505_ = lean_io_getenv(v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 1)
{
lean_object* v_val_1506_; 
lean_dec_ref(v_sysroot_1470_);
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v_cc_1474_ = v_val_1506_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
lean_dec(v___x_1505_);
lean_inc_ref(v_sysroot_1470_);
v___x_1507_ = l_Lake_leanCcExe(v_sysroot_1470_);
v___x_1508_ = l_System_FilePath_pathExists(v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref(v___x_1507_);
lean_dec_ref(v_sysroot_1470_);
v___x_1509_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1510_ = lean_io_getenv(v___x_1509_);
if (lean_obj_tag(v___x_1510_) == 1)
{
lean_object* v_val_1511_; 
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v_cc_1474_ = v_val_1511_;
goto v___jp_1473_;
}
else
{
lean_object* v_sysroot_1512_; lean_object* v_githash_1513_; lean_object* v_srcDir_1514_; lean_object* v_leanLibDir_1515_; lean_object* v_includeDir_1516_; lean_object* v_systemLibDir_1517_; lean_object* v_binDir_1518_; lean_object* v_lean_1519_; lean_object* v_leanir_1520_; lean_object* v_leanc_1521_; lean_object* v_leantar_1522_; lean_object* v_sharedDynlibs_1523_; lean_object* v_sharedDynlib_1524_; lean_object* v_ar_1525_; uint8_t v_customCc_1526_; lean_object* v_cFlags_1527_; lean_object* v_linkStaticFlags_1528_; lean_object* v_linkSharedFlags_1529_; lean_object* v_ccFlags_1530_; lean_object* v_ccLinkStaticFlags_1531_; lean_object* v_ccLinkSharedFlags_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v___x_1510_);
v_sysroot_1512_ = lean_ctor_get(v_i_1471_, 0);
v_githash_1513_ = lean_ctor_get(v_i_1471_, 1);
v_srcDir_1514_ = lean_ctor_get(v_i_1471_, 2);
v_leanLibDir_1515_ = lean_ctor_get(v_i_1471_, 3);
v_includeDir_1516_ = lean_ctor_get(v_i_1471_, 4);
v_systemLibDir_1517_ = lean_ctor_get(v_i_1471_, 5);
v_binDir_1518_ = lean_ctor_get(v_i_1471_, 6);
v_lean_1519_ = lean_ctor_get(v_i_1471_, 7);
v_leanir_1520_ = lean_ctor_get(v_i_1471_, 8);
v_leanc_1521_ = lean_ctor_get(v_i_1471_, 9);
v_leantar_1522_ = lean_ctor_get(v_i_1471_, 10);
v_sharedDynlibs_1523_ = lean_ctor_get(v_i_1471_, 11);
v_sharedDynlib_1524_ = lean_ctor_get(v_i_1471_, 12);
v_ar_1525_ = lean_ctor_get(v_i_1471_, 13);
v_customCc_1526_ = lean_ctor_get_uint8(v_i_1471_, sizeof(void*)*21);
v_cFlags_1527_ = lean_ctor_get(v_i_1471_, 15);
v_linkStaticFlags_1528_ = lean_ctor_get(v_i_1471_, 16);
v_linkSharedFlags_1529_ = lean_ctor_get(v_i_1471_, 17);
v_ccFlags_1530_ = lean_ctor_get(v_i_1471_, 18);
v_ccLinkStaticFlags_1531_ = lean_ctor_get(v_i_1471_, 19);
v_ccLinkSharedFlags_1532_ = lean_ctor_get(v_i_1471_, 20);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_i_1471_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v_i_1471_, 14);
lean_dec(v_unused_1541_);
v___x_1534_ = v_i_1471_;
v_isShared_1535_ = v_isSharedCheck_1540_;
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
lean_dec(v_i_1471_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1540_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 14, v___x_1536_);
v___x_1538_ = v___x_1534_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_sysroot_1512_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_githash_1513_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_srcDir_1514_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_leanLibDir_1515_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_includeDir_1516_);
lean_ctor_set(v_reuseFailAlloc_1539_, 5, v_systemLibDir_1517_);
lean_ctor_set(v_reuseFailAlloc_1539_, 6, v_binDir_1518_);
lean_ctor_set(v_reuseFailAlloc_1539_, 7, v_lean_1519_);
lean_ctor_set(v_reuseFailAlloc_1539_, 8, v_leanir_1520_);
lean_ctor_set(v_reuseFailAlloc_1539_, 9, v_leanc_1521_);
lean_ctor_set(v_reuseFailAlloc_1539_, 10, v_leantar_1522_);
lean_ctor_set(v_reuseFailAlloc_1539_, 11, v_sharedDynlibs_1523_);
lean_ctor_set(v_reuseFailAlloc_1539_, 12, v_sharedDynlib_1524_);
lean_ctor_set(v_reuseFailAlloc_1539_, 13, v_ar_1525_);
lean_ctor_set(v_reuseFailAlloc_1539_, 14, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 15, v_cFlags_1527_);
lean_ctor_set(v_reuseFailAlloc_1539_, 16, v_linkStaticFlags_1528_);
lean_ctor_set(v_reuseFailAlloc_1539_, 17, v_linkSharedFlags_1529_);
lean_ctor_set(v_reuseFailAlloc_1539_, 18, v_ccFlags_1530_);
lean_ctor_set(v_reuseFailAlloc_1539_, 19, v_ccLinkStaticFlags_1531_);
lean_ctor_set(v_reuseFailAlloc_1539_, 20, v_ccLinkSharedFlags_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1539_, sizeof(void*)*21, v_customCc_1526_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1470_, v_i_1471_, v___x_1507_);
lean_dec_ref(v_sysroot_1470_);
return v___x_1542_;
}
}
v___jp_1473_:
{
lean_object* v_sysroot_1475_; lean_object* v_githash_1476_; lean_object* v_srcDir_1477_; lean_object* v_leanLibDir_1478_; lean_object* v_includeDir_1479_; lean_object* v_systemLibDir_1480_; lean_object* v_binDir_1481_; lean_object* v_lean_1482_; lean_object* v_leanir_1483_; lean_object* v_leanc_1484_; lean_object* v_leantar_1485_; lean_object* v_sharedDynlibs_1486_; lean_object* v_sharedDynlib_1487_; lean_object* v_ar_1488_; uint8_t v_customCc_1489_; lean_object* v_cFlags_1490_; lean_object* v_linkStaticFlags_1491_; lean_object* v_linkSharedFlags_1492_; lean_object* v_ccFlags_1493_; lean_object* v_ccLinkStaticFlags_1494_; lean_object* v_ccLinkSharedFlags_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_sysroot_1475_ = lean_ctor_get(v_i_1471_, 0);
v_githash_1476_ = lean_ctor_get(v_i_1471_, 1);
v_srcDir_1477_ = lean_ctor_get(v_i_1471_, 2);
v_leanLibDir_1478_ = lean_ctor_get(v_i_1471_, 3);
v_includeDir_1479_ = lean_ctor_get(v_i_1471_, 4);
v_systemLibDir_1480_ = lean_ctor_get(v_i_1471_, 5);
v_binDir_1481_ = lean_ctor_get(v_i_1471_, 6);
v_lean_1482_ = lean_ctor_get(v_i_1471_, 7);
v_leanir_1483_ = lean_ctor_get(v_i_1471_, 8);
v_leanc_1484_ = lean_ctor_get(v_i_1471_, 9);
v_leantar_1485_ = lean_ctor_get(v_i_1471_, 10);
v_sharedDynlibs_1486_ = lean_ctor_get(v_i_1471_, 11);
v_sharedDynlib_1487_ = lean_ctor_get(v_i_1471_, 12);
v_ar_1488_ = lean_ctor_get(v_i_1471_, 13);
v_customCc_1489_ = lean_ctor_get_uint8(v_i_1471_, sizeof(void*)*21);
v_cFlags_1490_ = lean_ctor_get(v_i_1471_, 15);
v_linkStaticFlags_1491_ = lean_ctor_get(v_i_1471_, 16);
v_linkSharedFlags_1492_ = lean_ctor_get(v_i_1471_, 17);
v_ccFlags_1493_ = lean_ctor_get(v_i_1471_, 18);
v_ccLinkStaticFlags_1494_ = lean_ctor_get(v_i_1471_, 19);
v_ccLinkSharedFlags_1495_ = lean_ctor_get(v_i_1471_, 20);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_i_1471_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v_i_1471_, 14);
lean_dec(v_unused_1503_);
v___x_1497_ = v_i_1471_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1495_);
lean_inc(v_ccLinkStaticFlags_1494_);
lean_inc(v_ccFlags_1493_);
lean_inc(v_linkSharedFlags_1492_);
lean_inc(v_linkStaticFlags_1491_);
lean_inc(v_cFlags_1490_);
lean_inc(v_ar_1488_);
lean_inc(v_sharedDynlib_1487_);
lean_inc(v_sharedDynlibs_1486_);
lean_inc(v_leantar_1485_);
lean_inc(v_leanc_1484_);
lean_inc(v_leanir_1483_);
lean_inc(v_lean_1482_);
lean_inc(v_binDir_1481_);
lean_inc(v_systemLibDir_1480_);
lean_inc(v_includeDir_1479_);
lean_inc(v_leanLibDir_1478_);
lean_inc(v_srcDir_1477_);
lean_inc(v_githash_1476_);
lean_inc(v_sysroot_1475_);
lean_dec(v_i_1471_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 14, v_cc_1474_);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_sysroot_1475_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_githash_1476_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_srcDir_1477_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_leanLibDir_1478_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_includeDir_1479_);
lean_ctor_set(v_reuseFailAlloc_1501_, 5, v_systemLibDir_1480_);
lean_ctor_set(v_reuseFailAlloc_1501_, 6, v_binDir_1481_);
lean_ctor_set(v_reuseFailAlloc_1501_, 7, v_lean_1482_);
lean_ctor_set(v_reuseFailAlloc_1501_, 8, v_leanir_1483_);
lean_ctor_set(v_reuseFailAlloc_1501_, 9, v_leanc_1484_);
lean_ctor_set(v_reuseFailAlloc_1501_, 10, v_leantar_1485_);
lean_ctor_set(v_reuseFailAlloc_1501_, 11, v_sharedDynlibs_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 12, v_sharedDynlib_1487_);
lean_ctor_set(v_reuseFailAlloc_1501_, 13, v_ar_1488_);
lean_ctor_set(v_reuseFailAlloc_1501_, 14, v_cc_1474_);
lean_ctor_set(v_reuseFailAlloc_1501_, 15, v_cFlags_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 16, v_linkStaticFlags_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 17, v_linkSharedFlags_1492_);
lean_ctor_set(v_reuseFailAlloc_1501_, 18, v_ccFlags_1493_);
lean_ctor_set(v_reuseFailAlloc_1501_, 19, v_ccLinkStaticFlags_1494_);
lean_ctor_set(v_reuseFailAlloc_1501_, 20, v_ccLinkSharedFlags_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*21, v_customCc_1489_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc_0interp(lean_interpreter_value* stack)
{
lean_object* v_sysroot_1470_ = stack[0].m_obj;
lean_object* v_i_1471_ = stack[1].m_obj;
lean_object* v_res_1543_;
v_res_1543_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1470_, v_i_1471_);
stack->m_obj
 = v_res_1543_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1544_, lean_object* v_i_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1544_, v_i_1545_);
return v_res_1547_;
}
}
lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1548_, uint8_t v_collocated_1549_){
_start:
{
lean_object* v_githash_1552_; 
if (v_collocated_1549_ == 0)
{
lean_object* v___x_1578_; 
lean_inc_ref(v_sysroot_1548_);
v___x_1578_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1548_);
v_githash_1552_ = v___x_1578_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_githash;
v_githash_1552_ = v___x_1579_;
goto v___jp_1551_;
}
v___jp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_inc_ref_n(v_sysroot_1548_, 12);
v___x_1553_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1548_);
v___x_1554_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1555_ = l_System_FilePath_join(v_sysroot_1548_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1557_ = l_System_FilePath_join(v___x_1555_, v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1559_ = l_System_FilePath_join(v_sysroot_1548_, v___x_1558_);
lean_inc_ref(v___x_1559_);
v___x_1560_ = l_System_FilePath_join(v___x_1559_, v___x_1556_);
v___x_1561_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1562_ = l_System_FilePath_join(v_sysroot_1548_, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1564_ = l_System_FilePath_join(v_sysroot_1548_, v___x_1563_);
v___x_1565_ = l_Lake_leanExe(v_sysroot_1548_);
v___x_1566_ = l_Lake_leanirExe(v_sysroot_1548_);
v___x_1567_ = l_Lake_leancExe(v_sysroot_1548_);
v___x_1568_ = l_Lake_leantarExe(v_sysroot_1548_);
v___x_1569_ = l_Lake_leanSharedDynlibs(v_sysroot_1548_);
v___x_1570_ = l_Lake_leanSharedDynlib(v_sysroot_1548_);
v___x_1571_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1572_ = 1;
v___x_1573_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1574_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1575_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_1576_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1576_, 0, v_sysroot_1548_);
lean_ctor_set(v___x_1576_, 1, v_githash_1552_);
lean_ctor_set(v___x_1576_, 2, v___x_1557_);
lean_ctor_set(v___x_1576_, 3, v___x_1560_);
lean_ctor_set(v___x_1576_, 4, v___x_1562_);
lean_ctor_set(v___x_1576_, 5, v___x_1559_);
lean_ctor_set(v___x_1576_, 6, v___x_1564_);
lean_ctor_set(v___x_1576_, 7, v___x_1565_);
lean_ctor_set(v___x_1576_, 8, v___x_1566_);
lean_ctor_set(v___x_1576_, 9, v___x_1567_);
lean_ctor_set(v___x_1576_, 10, v___x_1568_);
lean_ctor_set(v___x_1576_, 11, v___x_1569_);
lean_ctor_set(v___x_1576_, 12, v___x_1570_);
lean_ctor_set(v___x_1576_, 13, v___x_1553_);
lean_ctor_set(v___x_1576_, 14, v___x_1571_);
lean_ctor_set(v___x_1576_, 15, v___x_1573_);
lean_ctor_set(v___x_1576_, 16, v___x_1574_);
lean_ctor_set(v___x_1576_, 17, v___x_1575_);
lean_ctor_set(v___x_1576_, 18, v___x_1573_);
lean_ctor_set(v___x_1576_, 19, v___x_1574_);
lean_ctor_set(v___x_1576_, 20, v___x_1575_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*21, v___x_1572_);
v___x_1577_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1548_, v___x_1576_);
return v___x_1577_;
}
}
}
LEAN_EXPORT void l_Lake_LeanInstall_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_sysroot_1548_ = stack[0].m_obj;
uint8_t v_collocated_1549_ = stack[1].m_num;
lean_object* v_res_1580_;
v_res_1580_ = l_Lake_LeanInstall_get(v_sysroot_1548_, v_collocated_1549_);
stack->m_obj
 = v_res_1580_;
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1581_, lean_object* v_collocated_1582_, lean_object* v_a_1583_){
_start:
{
uint8_t v_collocated_boxed_1584_; lean_object* v_res_1585_; 
v_collocated_boxed_1584_ = lean_unbox(v_collocated_1582_);
v_res_1585_ = l_Lake_LeanInstall_get(v_sysroot_1581_, v_collocated_boxed_1584_);
return v_res_1585_;
}
}
lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lake_findLeanSysroot_x3f(v_lean_1586_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_box(0);
return v___x_1589_;
}
else
{
lean_object* v_val_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1599_; 
v_val_1590_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1592_ = v___x_1588_;
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_val_1590_);
lean_dec(v___x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = 0;
v___x_1595_ = l_Lake_LeanInstall_get(v_val_1590_, v___x_1594_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_findLeanCmdInstall_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lean_1586_ = stack[0].m_obj;
lean_object* v_res_1600_;
v_res_1600_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1586_);
stack->m_obj
 = v_res_1600_;
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1601_);
return v_res_1603_;
}
}
lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_io_app_path();
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = l_System_FilePath_parent(v_a_1608_);
if (lean_obj_tag(v___x_1609_) == 1)
{
lean_object* v_val_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_n(v_val_1610_, 2);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1612_ = l_System_FilePath_join(v_val_1610_, v___x_1611_);
v___x_1613_ = l_System_FilePath_exeExtension;
v___x_1614_ = l_System_FilePath_addExtension(v___x_1612_, v___x_1613_);
v___x_1615_ = l_System_FilePath_pathExists(v___x_1614_);
lean_dec_ref(v___x_1614_);
if (v___x_1615_ == 0)
{
lean_dec(v_val_1610_);
goto v___jp_1605_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = l_System_FilePath_parent(v_val_1610_);
return v___x_1616_;
}
}
else
{
lean_dec(v___x_1609_);
goto v___jp_1605_;
}
}
else
{
lean_dec_ref_known(v___x_1607_, 1);
goto v___jp_1605_;
}
v___jp_1605_:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_box(0);
return v___x_1606_;
}
}
}
LEAN_EXPORT void l_Lake_findLakeLeanJointHome_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1617_;
v_res_1617_ = l_Lake_findLakeLeanJointHome_x3f();
stack->m_obj
 = v_res_1617_;
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_System_FilePath_parent(v_lake_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
return v___x_1621_;
}
else
{
lean_object* v_val_1622_; lean_object* v___x_1623_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_System_FilePath_parent(v_val_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
return v___x_1623_;
}
else
{
lean_object* v_val_1624_; lean_object* v___x_1625_; 
v_val_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = l_System_FilePath_parent(v_val_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
return v___x_1625_;
}
else
{
lean_object* v_val_1626_; lean_object* v___x_1627_; 
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = l_System_FilePath_parent(v_val_1626_);
return v___x_1627_;
}
}
}
}
}
lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1629_){
_start:
{
lean_object* v___x_1631_; 
lean_inc_ref(v_lake_1629_);
v___x_1631_ = l_Lake_lakeBuildHome_x3f(v_lake_1629_);
if (lean_obj_tag(v___x_1631_) == 1)
{
lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1656_; 
v_val_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1656_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1656_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v_lake_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1636_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1632_, 2);
v___x_1637_ = l_System_FilePath_join(v_val_1632_, v___x_1636_);
v___x_1638_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1637_);
v___x_1639_ = l_System_FilePath_join(v___x_1637_, v___x_1638_);
v___x_1640_ = l_Lake_defaultLeanLibDir;
v___x_1641_ = l_System_FilePath_join(v___x_1637_, v___x_1640_);
v___x_1642_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1643_ = 0;
v___x_1644_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref_n(v___x_1641_, 2);
v___x_1645_ = l_System_FilePath_join(v___x_1641_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1647_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1642_);
lean_ctor_set(v___x_1647_, 2, v___x_1646_);
lean_ctor_set(v___x_1647_, 3, v___x_1646_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*4, v___x_1643_);
v_lake_1648_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1648_, 0, v_val_1632_);
lean_ctor_set(v_lake_1648_, 1, v_val_1632_);
lean_ctor_set(v_lake_1648_, 2, v___x_1639_);
lean_ctor_set(v_lake_1648_, 3, v___x_1641_);
lean_ctor_set(v_lake_1648_, 4, v___x_1647_);
lean_ctor_set(v_lake_1648_, 5, v_lake_1629_);
v___x_1649_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1650_ = l_System_FilePath_join(v___x_1641_, v___x_1649_);
v___x_1651_ = l_System_FilePath_pathExists(v___x_1650_);
lean_dec_ref(v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_dec_ref_known(v_lake_1648_, 6);
lean_del_object(v___x_1634_);
v___x_1652_ = lean_box(0);
return v___x_1652_;
}
else
{
lean_object* v___x_1654_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_lake_1648_);
v___x_1654_ = v___x_1634_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_lake_1648_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v___x_1657_; 
lean_dec(v___x_1631_);
lean_dec_ref(v_lake_1629_);
v___x_1657_ = lean_box(0);
return v___x_1657_;
}
}
}
LEAN_EXPORT void l_Lake_getLakeInstall_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lake_1629_ = stack[0].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Lake_getLakeInstall_x3f(v_lake_1629_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lake_getLakeInstall_x3f(v_lake_1659_);
return v_res_1661_;
}
}
lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v_lean_1666_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1680_ = lean_io_getenv(v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 1)
{
lean_object* v_val_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1690_; 
v_val_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_val_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1685_ = 0;
v___x_1686_ = l_Lake_LeanInstall_get(v_val_1681_, v___x_1685_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1686_);
v___x_1688_ = v___x_1683_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v___x_1680_);
v___x_1691_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1692_ = lean_io_getenv(v___x_1691_);
if (lean_obj_tag(v___x_1692_) == 1)
{
lean_object* v_val_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_startInclusive_1698_; lean_object* v_endExclusive_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_val_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc_n(v_val_1693_, 2);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = lean_string_utf8_byte_size(v_val_1693_);
v___x_1696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1696_, 0, v_val_1693_);
lean_ctor_set(v___x_1696_, 1, v___x_1694_);
lean_ctor_set(v___x_1696_, 2, v___x_1695_);
v___x_1697_ = l_String_Slice_trimAscii(v___x_1696_);
v_startInclusive_1698_ = lean_ctor_get(v___x_1697_, 1);
lean_inc(v_startInclusive_1698_);
v_endExclusive_1699_ = lean_ctor_get(v___x_1697_, 2);
lean_inc(v_endExclusive_1699_);
lean_dec_ref(v___x_1697_);
v___x_1700_ = lean_nat_sub(v_endExclusive_1699_, v_startInclusive_1698_);
lean_dec(v_startInclusive_1698_);
lean_dec(v_endExclusive_1699_);
v___x_1701_ = lean_nat_dec_eq(v___x_1700_, v___x_1694_);
lean_dec(v___x_1700_);
if (v___x_1701_ == 0)
{
v_lean_1666_ = v_val_1693_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1702_; 
lean_dec(v_val_1693_);
v___x_1702_ = lean_box(0);
return v___x_1702_;
}
}
else
{
lean_object* v___x_1703_; 
lean_dec(v___x_1692_);
v___x_1703_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v_lean_1666_ = v___x_1703_;
goto v___jp_1665_;
}
}
v___jp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lake_findLeanSysroot_x3f(v_lean_1666_);
if (lean_obj_tag(v___x_1667_) == 1)
{
lean_object* v_val_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1677_; 
v_val_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_val_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1672_ = 0;
v___x_1673_ = l_Lake_LeanInstall_get(v_val_1668_, v___x_1672_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v___x_1678_; 
lean_dec(v___x_1667_);
v___x_1678_ = lean_box(0);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT void l_Lake_findLeanInstall_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1704_;
v_res_1704_ = l_Lake_findLeanInstall_x3f();
stack->m_obj
 = v_res_1704_;
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lake_findLeanInstall_x3f();
return v_res_1706_;
}
}
lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_io_app_path();
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = l_Lake_getLakeInstall_x3f(v_a_1737_);
if (lean_obj_tag(v___x_1738_) == 1)
{
return v___x_1738_;
}
else
{
lean_dec(v___x_1738_);
goto v___jp_1709_;
}
}
else
{
lean_dec_ref_known(v___x_1736_, 1);
goto v___jp_1709_;
}
v___jp_1709_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1711_ = lean_io_getenv(v___x_1710_);
if (lean_obj_tag(v___x_1711_) == 1)
{
lean_object* v_val_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1734_; 
v_val_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1734_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_val_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1734_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1716_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1712_, 2);
v___x_1717_ = l_System_FilePath_join(v_val_1712_, v___x_1716_);
v___x_1718_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1717_);
v___x_1719_ = l_System_FilePath_join(v___x_1717_, v___x_1718_);
v___x_1720_ = l_Lake_defaultLeanLibDir;
v___x_1721_ = l_System_FilePath_join(v___x_1717_, v___x_1720_);
v___x_1722_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1723_ = 0;
v___x_1724_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref(v___x_1721_);
v___x_1725_ = l_System_FilePath_join(v___x_1721_, v___x_1724_);
v___x_1726_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1727_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1722_);
lean_ctor_set(v___x_1727_, 2, v___x_1726_);
lean_ctor_set(v___x_1727_, 3, v___x_1726_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*4, v___x_1723_);
v___x_1728_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1719_);
v___x_1729_ = l_System_FilePath_join(v___x_1719_, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1730_, 0, v_val_1712_);
lean_ctor_set(v___x_1730_, 1, v_val_1712_);
lean_ctor_set(v___x_1730_, 2, v___x_1719_);
lean_ctor_set(v___x_1730_, 3, v___x_1721_);
lean_ctor_set(v___x_1730_, 4, v___x_1727_);
lean_ctor_set(v___x_1730_, 5, v___x_1729_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1730_);
v___x_1732_ = v___x_1714_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v___x_1735_; 
lean_dec(v___x_1711_);
v___x_1735_ = lean_box(0);
return v___x_1735_;
}
}
}
}
LEAN_EXPORT void l_Lake_findLakeInstall_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1739_;
v_res_1739_ = l_Lake_findLakeInstall_x3f();
stack->m_obj
 = v_res_1739_;
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lake_findLakeInstall_x3f();
return v_res_1741_;
}
}
lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = l_Lake_findElanInstall_x3f();
v___x_1745_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1745_) == 1)
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1803_; 
v_val_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1803_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1803_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1751_ = lean_io_getenv(v___x_1750_);
if (lean_obj_tag(v___x_1751_) == 0)
{
goto v___jp_1752_;
}
else
{
lean_object* v_val_1762_; lean_object* v___x_1763_; 
v_val_1762_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1763_ = l_Lake_envToBool_x3f(v_val_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
goto v___jp_1752_;
}
else
{
lean_object* v_val_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1802_; 
v_val_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1802_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_val_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1802_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_unbox(v_val_1764_);
if (v___x_1768_ == 0)
{
lean_del_object(v___x_1766_);
lean_dec(v_val_1764_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_del_object(v___x_1748_);
v___x_1769_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1770_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
lean_inc_n(v_val_1746_, 10);
v___x_1771_ = l_System_FilePath_join(v_val_1746_, v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1773_ = l_System_FilePath_join(v___x_1771_, v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1775_ = l_System_FilePath_join(v_val_1746_, v___x_1774_);
lean_inc_ref(v___x_1775_);
v___x_1776_ = l_System_FilePath_join(v___x_1775_, v___x_1772_);
v___x_1777_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1778_ = l_System_FilePath_join(v_val_1746_, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1780_ = l_System_FilePath_join(v_val_1746_, v___x_1779_);
v___x_1781_ = l_Lake_leanExe(v_val_1746_);
v___x_1782_ = l_Lake_leanirExe(v_val_1746_);
v___x_1783_ = l_Lake_leancExe(v_val_1746_);
v___x_1784_ = l_Lake_leantarExe(v_val_1746_);
v___x_1785_ = l_Lake_leanSharedDynlibs(v_val_1746_);
v___x_1786_ = l_Lake_leanSharedDynlib(v_val_1746_);
v___x_1787_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_1788_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1789_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1790_ = lean_unbox(v_val_1764_);
v___x_1791_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1790_);
v___x_1792_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
lean_inc_ref(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1793_, 0, v_val_1746_);
lean_ctor_set(v___x_1793_, 1, v___x_1769_);
lean_ctor_set(v___x_1793_, 2, v___x_1773_);
lean_ctor_set(v___x_1793_, 3, v___x_1776_);
lean_ctor_set(v___x_1793_, 4, v___x_1778_);
lean_ctor_set(v___x_1793_, 5, v___x_1775_);
lean_ctor_set(v___x_1793_, 6, v___x_1780_);
lean_ctor_set(v___x_1793_, 7, v___x_1781_);
lean_ctor_set(v___x_1793_, 8, v___x_1782_);
lean_ctor_set(v___x_1793_, 9, v___x_1783_);
lean_ctor_set(v___x_1793_, 10, v___x_1784_);
lean_ctor_set(v___x_1793_, 11, v___x_1785_);
lean_ctor_set(v___x_1793_, 12, v___x_1786_);
lean_ctor_set(v___x_1793_, 13, v___x_1787_);
lean_ctor_set(v___x_1793_, 14, v___x_1788_);
lean_ctor_set(v___x_1793_, 15, v___x_1789_);
lean_ctor_set(v___x_1793_, 16, v___x_1791_);
lean_ctor_set(v___x_1793_, 17, v___x_1792_);
lean_ctor_set(v___x_1793_, 18, v___x_1789_);
lean_ctor_set(v___x_1793_, 19, v___x_1791_);
lean_ctor_set(v___x_1793_, 20, v___x_1792_);
v___x_1794_ = lean_unbox(v_val_1764_);
lean_dec(v_val_1764_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*21, v___x_1794_);
v___x_1795_ = l_Lake_LakeInstall_ofLean(v___x_1793_);
v___x_1796_ = l_Lake_findLeanInstall_x3f();
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1795_);
v___x_1798_ = v___x_1766_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1795_);
v___x_1798_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1796_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1744_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
return v___x_1800_;
}
}
}
}
}
v___jp_1752_:
{
uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1753_ = 1;
v___x_1754_ = l_Lake_LeanInstall_get(v_val_1746_, v___x_1753_);
lean_inc_ref(v___x_1754_);
v___x_1755_ = l_Lake_LakeInstall_ofLean(v___x_1754_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1754_);
v___x_1757_ = v___x_1748_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1754_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1755_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1744_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
return v___x_1760_;
}
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec(v___x_1745_);
v___x_1804_ = l_Lake_findLeanInstall_x3f();
v___x_1805_ = l_Lake_findLakeInstall_x3f();
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1744_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
return v___x_1807_;
}
}
}
LEAN_EXPORT void l_Lake_findInstall_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1808_;
v_res_1808_ = l_Lake_findInstall_x3f();
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lake_findInstall_x3f();
return v_res_1810_;
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
