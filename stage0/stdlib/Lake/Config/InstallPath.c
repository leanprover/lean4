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
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs(lean_object* v_f_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_init_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_lean1_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_lean2_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_lean_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_388_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_389_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
lean_inc_ref_n(v_f_387_, 3);
v_init_390_ = lean_apply_2(v_f_387_, v___x_388_, v___x_389_);
v___x_391_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_mk_empty_array_with_capacity(v___x_392_);
lean_inc_ref_n(v_init_390_, 3);
v___x_394_ = lean_array_push(v___x_393_, v_init_390_);
v_lean1_395_ = lean_apply_2(v_f_387_, v___x_391_, v___x_394_);
v___x_396_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_397_ = lean_unsigned_to_nat(2u);
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_397_);
lean_inc_ref_n(v_lean1_395_, 2);
v___x_399_ = lean_array_push(v___x_398_, v_lean1_395_);
v___x_400_ = lean_array_push(v___x_399_, v_init_390_);
v_lean2_401_ = lean_apply_2(v_f_387_, v___x_396_, v___x_400_);
v___x_402_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_403_ = lean_unsigned_to_nat(3u);
v___x_404_ = lean_mk_empty_array_with_capacity(v___x_403_);
lean_inc_ref(v_lean2_401_);
v___x_405_ = lean_array_push(v___x_404_, v_lean2_401_);
v___x_406_ = lean_array_push(v___x_405_, v_lean1_395_);
v___x_407_ = lean_array_push(v___x_406_, v_init_390_);
v_lean_408_ = lean_apply_2(v_f_387_, v___x_402_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(4u);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
v___x_411_ = lean_array_push(v___x_410_, v_lean_408_);
v___x_412_ = lean_array_push(v___x_411_, v_lean2_401_);
v___x_413_ = lean_array_push(v___x_412_, v_lean1_395_);
v___x_414_ = lean_array_push(v___x_413_, v_init_390_);
return v___x_414_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = l_Lake_sharedLibExt;
v___x_417_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__0));
v___x_418_ = lean_string_append(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = l_Lake_sharedLibExt;
v___x_421_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__2));
v___x_422_ = lean_string_append(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__5(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = l_Lake_sharedLibExt;
v___x_425_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__4));
v___x_426_ = lean_string_append(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__7(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = l_Lake_sharedLibExt;
v___x_429_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__6));
v___x_430_ = lean_string_append(v___x_429_, v___x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlibs(lean_object* v_sysroot_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_System_Platform_isWindows;
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_init_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_lean1_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_lean2_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_lean_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_437_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_438_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_439_ = l_System_FilePath_join(v_sysroot_435_, v___x_438_);
v___x_440_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_441_ = l_System_FilePath_join(v___x_439_, v___x_440_);
v___x_442_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__1, &l_Lake_leanSharedDynlibs___closed__1_once, _init_l_Lake_leanSharedDynlibs___closed__1);
lean_inc_ref_n(v___x_441_, 3);
v___x_443_ = l_System_FilePath_join(v___x_441_, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v_init_445_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_445_, 0, v___x_443_);
lean_ctor_set(v_init_445_, 1, v___x_437_);
lean_ctor_set(v_init_445_, 2, v___x_444_);
lean_ctor_set(v_init_445_, 3, v___x_444_);
lean_ctor_set_uint8(v_init_445_, sizeof(void*)*4, v___x_436_);
v___x_446_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_447_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__3, &l_Lake_leanSharedDynlibs___closed__3_once, _init_l_Lake_leanSharedDynlibs___closed__3);
v___x_448_ = l_System_FilePath_join(v___x_441_, v___x_447_);
v_lean1_449_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_449_, 0, v___x_448_);
lean_ctor_set(v_lean1_449_, 1, v___x_446_);
lean_ctor_set(v_lean1_449_, 2, v___x_444_);
lean_ctor_set(v_lean1_449_, 3, v___x_444_);
lean_ctor_set_uint8(v_lean1_449_, sizeof(void*)*4, v___x_436_);
v___x_450_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_451_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__5, &l_Lake_leanSharedDynlibs___closed__5_once, _init_l_Lake_leanSharedDynlibs___closed__5);
v___x_452_ = l_System_FilePath_join(v___x_441_, v___x_451_);
v_lean2_453_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_453_, 0, v___x_452_);
lean_ctor_set(v_lean2_453_, 1, v___x_450_);
lean_ctor_set(v_lean2_453_, 2, v___x_444_);
lean_ctor_set(v_lean2_453_, 3, v___x_444_);
lean_ctor_set_uint8(v_lean2_453_, sizeof(void*)*4, v___x_436_);
v___x_454_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_455_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__7, &l_Lake_leanSharedDynlibs___closed__7_once, _init_l_Lake_leanSharedDynlibs___closed__7);
v___x_456_ = l_System_FilePath_join(v___x_441_, v___x_455_);
v_lean_457_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_457_, 0, v___x_456_);
lean_ctor_set(v_lean_457_, 1, v___x_454_);
lean_ctor_set(v_lean_457_, 2, v___x_444_);
lean_ctor_set(v_lean_457_, 3, v___x_444_);
lean_ctor_set_uint8(v_lean_457_, sizeof(void*)*4, v___x_436_);
v___x_458_ = lean_unsigned_to_nat(4u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_array_push(v___x_459_, v_lean_457_);
v___x_461_ = lean_array_push(v___x_460_, v_lean2_453_);
v___x_462_ = lean_array_push(v___x_461_, v_lean1_449_);
v___x_463_ = lean_array_push(v___x_462_, v_init_445_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v_init_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_lean1_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_lean2_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_lean_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_464_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_465_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_466_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_467_ = l_System_FilePath_join(v_sysroot_435_, v___x_466_);
v___x_468_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__8));
lean_inc_ref_n(v___x_467_, 3);
v___x_469_ = l_System_FilePath_join(v___x_467_, v___x_468_);
v___x_470_ = 0;
v_init_471_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_471_, 0, v___x_469_);
lean_ctor_set(v_init_471_, 1, v___x_464_);
lean_ctor_set(v_init_471_, 2, v___x_465_);
lean_ctor_set(v_init_471_, 3, v___x_465_);
lean_ctor_set_uint8(v_init_471_, sizeof(void*)*4, v___x_470_);
v___x_472_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_mk_empty_array_with_capacity(v___x_473_);
lean_inc_ref_n(v_init_471_, 3);
v___x_475_ = lean_array_push(v___x_474_, v_init_471_);
v___x_476_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__9));
v___x_477_ = l_System_FilePath_join(v___x_467_, v___x_476_);
v_lean1_478_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_478_, 0, v___x_477_);
lean_ctor_set(v_lean1_478_, 1, v___x_472_);
lean_ctor_set(v_lean1_478_, 2, v___x_475_);
lean_ctor_set(v_lean1_478_, 3, v___x_465_);
lean_ctor_set_uint8(v_lean1_478_, sizeof(void*)*4, v___x_470_);
v___x_479_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = lean_mk_empty_array_with_capacity(v___x_480_);
lean_inc_ref_n(v_lean1_478_, 2);
v___x_482_ = lean_array_push(v___x_481_, v_lean1_478_);
v___x_483_ = lean_array_push(v___x_482_, v_init_471_);
v___x_484_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__10));
v___x_485_ = l_System_FilePath_join(v___x_467_, v___x_484_);
v_lean2_486_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_486_, 0, v___x_485_);
lean_ctor_set(v_lean2_486_, 1, v___x_479_);
lean_ctor_set(v_lean2_486_, 2, v___x_483_);
lean_ctor_set(v_lean2_486_, 3, v___x_465_);
lean_ctor_set_uint8(v_lean2_486_, sizeof(void*)*4, v___x_470_);
v___x_487_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_488_ = lean_unsigned_to_nat(3u);
v___x_489_ = lean_mk_empty_array_with_capacity(v___x_488_);
lean_inc_ref(v_lean2_486_);
v___x_490_ = lean_array_push(v___x_489_, v_lean2_486_);
v___x_491_ = lean_array_push(v___x_490_, v_lean1_478_);
v___x_492_ = lean_array_push(v___x_491_, v_init_471_);
v___x_493_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__11));
v___x_494_ = l_System_FilePath_join(v___x_467_, v___x_493_);
v_lean_495_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_495_, 0, v___x_494_);
lean_ctor_set(v_lean_495_, 1, v___x_487_);
lean_ctor_set(v_lean_495_, 2, v___x_492_);
lean_ctor_set(v_lean_495_, 3, v___x_465_);
lean_ctor_set_uint8(v_lean_495_, sizeof(void*)*4, v___x_470_);
v___x_496_ = lean_unsigned_to_nat(4u);
v___x_497_ = lean_mk_empty_array_with_capacity(v___x_496_);
v___x_498_ = lean_array_push(v___x_497_, v_lean_495_);
v___x_499_ = lean_array_push(v___x_498_, v_lean2_486_);
v___x_500_ = lean_array_push(v___x_499_, v_lean1_478_);
v___x_501_ = lean_array_push(v___x_500_, v_init_471_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlib(lean_object* v_sysroot_502_){
_start:
{
lean_object* v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = l_Lake_leanSharedDynlibs(v_sysroot_502_);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = lean_array_uget(v___x_503_, v___x_504_);
lean_dec_ref(v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = l_Lake_sharedLibExt;
v___x_508_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_509_ = l_System_FilePath_addExtension(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_510_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = l_Lake_sharedLibExt;
v___x_513_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_514_ = l_System_FilePath_addExtension(v___x_513_, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_515_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_518_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_519_ = l_System_FilePath_join(v___x_518_, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_521_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
v___x_522_ = l_System_FilePath_join(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_524_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_525_ = l_System_FilePath_join(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_527_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_528_ = l_System_FilePath_join(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_531_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_532_ = l_System_FilePath_join(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__7(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_534_ = l_Lake_leanExe(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__8(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_536_ = l_Lake_leanirExe(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__9(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_538_ = l_Lake_leancExe(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__10(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_540_ = l_Lake_leantarExe(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__11(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_542_ = l_Lake_leanSharedDynlibs(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__12(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_544_ = l_Lake_leanSharedDynlib(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__16(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_549_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_550_ = lean_array_push(v___x_549_, v___x_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__17(void){
_start:
{
uint8_t v___x_551_; lean_object* v___x_552_; 
v___x_551_ = 1;
v___x_552_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__18(void){
_start:
{
uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_553_ = 0;
v___x_554_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__19(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_555_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_556_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_557_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_558_ = 1;
v___x_559_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_560_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_561_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__12, &l_Lake_instInhabitedLeanInstall_default___closed__12_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__12);
v___x_562_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_563_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__10, &l_Lake_instInhabitedLeanInstall_default___closed__10_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__10);
v___x_564_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__9, &l_Lake_instInhabitedLeanInstall_default___closed__9_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__9);
v___x_565_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__8, &l_Lake_instInhabitedLeanInstall_default___closed__8_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__8);
v___x_566_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__7, &l_Lake_instInhabitedLeanInstall_default___closed__7_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__7);
v___x_567_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_568_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_569_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
v___x_570_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_571_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__2, &l_Lake_instInhabitedLeanInstall_default___closed__2_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__2);
v___x_572_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_573_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_ctor_set(v___x_573_, 2, v___x_571_);
lean_ctor_set(v___x_573_, 3, v___x_570_);
lean_ctor_set(v___x_573_, 4, v___x_569_);
lean_ctor_set(v___x_573_, 5, v___x_568_);
lean_ctor_set(v___x_573_, 6, v___x_567_);
lean_ctor_set(v___x_573_, 7, v___x_566_);
lean_ctor_set(v___x_573_, 8, v___x_565_);
lean_ctor_set(v___x_573_, 9, v___x_564_);
lean_ctor_set(v___x_573_, 10, v___x_563_);
lean_ctor_set(v___x_573_, 11, v___x_562_);
lean_ctor_set(v___x_573_, 12, v___x_561_);
lean_ctor_set(v___x_573_, 13, v___x_560_);
lean_ctor_set(v___x_573_, 14, v___x_559_);
lean_ctor_set(v___x_573_, 15, v___x_557_);
lean_ctor_set(v___x_573_, 16, v___x_556_);
lean_ctor_set(v___x_573_, 17, v___x_555_);
lean_ctor_set(v___x_573_, 18, v___x_557_);
lean_ctor_set(v___x_573_, 19, v___x_556_);
lean_ctor_set(v___x_573_, 20, v___x_555_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*21, v___x_558_);
return v___x_573_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
return v___x_574_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_dec(v_x_576_);
return v_x_577_;
}
else
{
lean_object* v_head_579_; lean_object* v_tail_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_591_; 
v_head_579_ = lean_ctor_get(v_x_578_, 0);
v_tail_580_ = lean_ctor_get(v_x_578_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_591_ == 0)
{
v___x_582_ = v_x_578_;
v_isShared_583_ = v_isSharedCheck_591_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_tail_580_);
lean_inc(v_head_579_);
lean_dec(v_x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_591_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
lean_inc(v_x_576_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 5);
lean_ctor_set(v___x_582_, 1, v_x_576_);
lean_ctor_set(v___x_582_, 0, v_x_577_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_x_577_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_x_576_);
v___x_585_ = v_reuseFailAlloc_590_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = l_String_quote(v_head_579_);
v___x_587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_585_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v_x_577_ = v___x_588_;
v_x_578_ = v_tail_580_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_dec(v_x_592_);
return v_x_593_;
}
else
{
lean_object* v_head_595_; lean_object* v_tail_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_607_; 
v_head_595_ = lean_ctor_get(v_x_594_, 0);
v_tail_596_ = lean_ctor_get(v_x_594_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_607_ == 0)
{
v___x_598_ = v_x_594_;
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_tail_596_);
lean_inc(v_head_595_);
lean_dec(v_x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
lean_inc(v_x_592_);
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 5);
lean_ctor_set(v___x_598_, 1, v_x_592_);
lean_ctor_set(v___x_598_, 0, v_x_593_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_x_593_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_x_592_);
v___x_601_ = v_reuseFailAlloc_606_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = l_String_quote(v_head_595_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(v_x_592_, v___x_604_, v_tail_596_);
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(lean_object* v___y_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = l_String_quote(v___y_608_);
v___x_610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v___x_613_; 
lean_dec(v_x_612_);
v___x_613_ = lean_box(0);
return v___x_613_;
}
else
{
lean_object* v_tail_614_; 
v_tail_614_ = lean_ctor_get(v_x_611_, 1);
if (lean_obj_tag(v_tail_614_) == 0)
{
lean_object* v_head_615_; lean_object* v___x_616_; 
lean_dec(v_x_612_);
v_head_615_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_head_615_);
lean_dec_ref_known(v_x_611_, 2);
v___x_616_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_615_);
return v___x_616_;
}
else
{
lean_object* v_head_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_inc(v_tail_614_);
v_head_617_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_head_617_);
lean_dec_ref_known(v_x_611_, 2);
v___x_618_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_617_);
v___x_619_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(v_x_612_, v___x_618_, v_tail_614_);
return v___x_619_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0));
v___x_626_ = lean_string_length(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3);
v___x_628_ = lean_nat_to_int(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(lean_object* v_xs_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_array_get_size(v_xs_636_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_nat_dec_eq(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_640_ = lean_array_to_list(v_xs_636_);
v___x_641_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_642_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(v___x_640_, v___x_641_);
v___x_643_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_644_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_642_);
v___x_646_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_643_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Std_Format_fill(v___x_648_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; 
lean_dec_ref(v_xs_636_);
v___x_650_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_dec(v_x_651_);
return v_x_652_;
}
else
{
lean_object* v_head_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_665_; 
v_head_654_ = lean_ctor_get(v_x_653_, 0);
v_tail_655_ = lean_ctor_get(v_x_653_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_665_ == 0)
{
v___x_657_ = v_x_653_;
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_head_654_);
lean_dec(v_x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
lean_inc(v_x_651_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 5);
lean_ctor_set(v___x_657_, 1, v_x_651_);
lean_ctor_set(v___x_657_, 0, v_x_652_);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_x_652_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_x_651_);
v___x_660_ = v_reuseFailAlloc_664_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = l_Lake_instReprDynlib_repr___redArg(v_head_654_);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v_x_652_ = v___x_662_;
v_x_653_ = v_tail_655_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_dec(v_x_666_);
return v_x_667_;
}
else
{
lean_object* v_head_669_; lean_object* v_tail_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_680_; 
v_head_669_ = lean_ctor_get(v_x_668_, 0);
v_tail_670_ = lean_ctor_get(v_x_668_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_680_ == 0)
{
v___x_672_ = v_x_668_;
v_isShared_673_ = v_isSharedCheck_680_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_tail_670_);
lean_inc(v_head_669_);
lean_dec(v_x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_680_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
lean_inc(v_x_666_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 5);
lean_ctor_set(v___x_672_, 1, v_x_666_);
lean_ctor_set(v___x_672_, 0, v_x_667_);
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_x_667_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_x_666_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = l_Lake_instReprDynlib_repr___redArg(v_head_669_);
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(v_x_666_, v___x_677_, v_tail_670_);
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_object* v___x_683_; 
lean_dec(v_x_682_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v_tail_684_; 
v_tail_684_ = lean_ctor_get(v_x_681_, 1);
if (lean_obj_tag(v_tail_684_) == 0)
{
lean_object* v_head_685_; lean_object* v___x_686_; 
lean_dec(v_x_682_);
v_head_685_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_head_685_);
lean_dec_ref_known(v_x_681_, 2);
v___x_686_ = l_Lake_instReprDynlib_repr___redArg(v_head_685_);
return v___x_686_;
}
else
{
lean_object* v_head_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc(v_tail_684_);
v_head_687_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_head_687_);
lean_dec_ref_known(v_x_681_, 2);
v___x_688_ = l_Lake_instReprDynlib_repr___redArg(v_head_687_);
v___x_689_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_682_, v___x_688_, v_tail_684_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_691_ = lean_array_get_size(v_xs_690_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_nat_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_694_ = lean_array_to_list(v_xs_690_);
v___x_695_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_696_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_694_, v___x_695_);
v___x_697_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_698_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_696_);
v___x_700_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = l_Std_Format_fill(v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec_ref(v_xs_690_);
v___x_704_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_704_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(11u);
v___x_715_ = lean_nat_to_int(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(14u);
v___x_726_ = lean_nat_to_int(v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_unsigned_to_nat(16u);
v___x_734_ = lean_nat_to_int(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(9u);
v___x_742_ = lean_nat_to_int(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(6u);
v___x_754_ = lean_nat_to_int(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(12u);
v___x_761_ = lean_nat_to_int(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(19u);
v___x_769_ = lean_nat_to_int(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(21u);
v___x_780_ = lean_nat_to_int(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_784_){
_start:
{
lean_object* v_sysroot_785_; lean_object* v_githash_786_; lean_object* v_srcDir_787_; lean_object* v_leanLibDir_788_; lean_object* v_includeDir_789_; lean_object* v_systemLibDir_790_; lean_object* v_binDir_791_; lean_object* v_lean_792_; lean_object* v_leanir_793_; lean_object* v_leanc_794_; lean_object* v_leantar_795_; lean_object* v_sharedDynlibs_796_; lean_object* v_sharedDynlib_797_; lean_object* v_ar_798_; lean_object* v_cc_799_; uint8_t v_customCc_800_; lean_object* v_cFlags_801_; lean_object* v_linkStaticFlags_802_; lean_object* v_linkSharedFlags_803_; lean_object* v_ccFlags_804_; lean_object* v_ccLinkStaticFlags_805_; lean_object* v_ccLinkSharedFlags_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_sysroot_785_ = lean_ctor_get(v_x_784_, 0);
lean_inc_ref(v_sysroot_785_);
v_githash_786_ = lean_ctor_get(v_x_784_, 1);
lean_inc_ref(v_githash_786_);
v_srcDir_787_ = lean_ctor_get(v_x_784_, 2);
lean_inc_ref(v_srcDir_787_);
v_leanLibDir_788_ = lean_ctor_get(v_x_784_, 3);
lean_inc_ref(v_leanLibDir_788_);
v_includeDir_789_ = lean_ctor_get(v_x_784_, 4);
lean_inc_ref(v_includeDir_789_);
v_systemLibDir_790_ = lean_ctor_get(v_x_784_, 5);
lean_inc_ref(v_systemLibDir_790_);
v_binDir_791_ = lean_ctor_get(v_x_784_, 6);
lean_inc_ref(v_binDir_791_);
v_lean_792_ = lean_ctor_get(v_x_784_, 7);
lean_inc_ref(v_lean_792_);
v_leanir_793_ = lean_ctor_get(v_x_784_, 8);
lean_inc_ref(v_leanir_793_);
v_leanc_794_ = lean_ctor_get(v_x_784_, 9);
lean_inc_ref(v_leanc_794_);
v_leantar_795_ = lean_ctor_get(v_x_784_, 10);
lean_inc_ref(v_leantar_795_);
v_sharedDynlibs_796_ = lean_ctor_get(v_x_784_, 11);
lean_inc_ref(v_sharedDynlibs_796_);
v_sharedDynlib_797_ = lean_ctor_get(v_x_784_, 12);
lean_inc_ref(v_sharedDynlib_797_);
v_ar_798_ = lean_ctor_get(v_x_784_, 13);
lean_inc_ref(v_ar_798_);
v_cc_799_ = lean_ctor_get(v_x_784_, 14);
lean_inc_ref(v_cc_799_);
v_customCc_800_ = lean_ctor_get_uint8(v_x_784_, sizeof(void*)*21);
v_cFlags_801_ = lean_ctor_get(v_x_784_, 15);
lean_inc_ref(v_cFlags_801_);
v_linkStaticFlags_802_ = lean_ctor_get(v_x_784_, 16);
lean_inc_ref(v_linkStaticFlags_802_);
v_linkSharedFlags_803_ = lean_ctor_get(v_x_784_, 17);
lean_inc_ref(v_linkSharedFlags_803_);
v_ccFlags_804_ = lean_ctor_get(v_x_784_, 18);
lean_inc_ref(v_ccFlags_804_);
v_ccLinkStaticFlags_805_ = lean_ctor_get(v_x_784_, 19);
lean_inc_ref(v_ccLinkStaticFlags_805_);
v_ccLinkSharedFlags_806_ = lean_ctor_get(v_x_784_, 20);
lean_inc_ref(v_ccLinkSharedFlags_806_);
lean_dec_ref(v_x_784_);
v___x_807_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_808_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_809_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_812_ = l_String_quote(v_sysroot_785_);
v___x_813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Repr_addAppParen(v___x_814_, v___x_810_);
v___x_816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_809_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = 0;
v___x_818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_808_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_box(1);
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_807_);
v___x_827_ = l_String_quote(v_githash_786_);
v___x_828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_809_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*1, v___x_817_);
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_826_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_820_);
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_822_);
v___x_834_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___x_807_);
v___x_837_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_838_ = l_String_quote(v_srcDir_787_);
v___x_839_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_811_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Repr_addAppParen(v___x_840_, v___x_810_);
v___x_842_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_837_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v___x_817_);
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_836_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_820_);
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_822_);
v___x_847_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_807_);
v___x_850_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_851_ = l_String_quote(v_leanLibDir_788_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_811_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Repr_addAppParen(v___x_853_, v___x_810_);
v___x_855_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_850_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_817_);
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_849_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_820_);
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_822_);
v___x_860_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_807_);
v___x_863_ = l_String_quote(v_includeDir_789_);
v___x_864_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
v___x_865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_811_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Repr_addAppParen(v___x_865_, v___x_810_);
v___x_867_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_850_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*1, v___x_817_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_862_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_820_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_822_);
v___x_872_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_807_);
v___x_875_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_876_ = l_String_quote(v_systemLibDir_790_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
v___x_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_811_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Repr_addAppParen(v___x_878_, v___x_810_);
v___x_880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_875_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_817_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_874_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_820_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_822_);
v___x_885_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_807_);
v___x_888_ = l_String_quote(v_binDir_791_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_811_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Repr_addAppParen(v___x_890_, v___x_810_);
v___x_892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_837_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_817_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_887_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_820_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_822_);
v___x_897_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_807_);
v___x_900_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_901_ = l_String_quote(v_lean_792_);
v___x_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_811_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Repr_addAppParen(v___x_903_, v___x_810_);
v___x_905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_900_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*1, v___x_817_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_899_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_820_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_822_);
v___x_910_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_807_);
v___x_913_ = l_String_quote(v_leanir_793_);
v___x_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_811_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Repr_addAppParen(v___x_915_, v___x_810_);
v___x_917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_837_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*1, v___x_817_);
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_912_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_820_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_822_);
v___x_922_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_807_);
v___x_925_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_926_ = l_String_quote(v_leanc_794_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_811_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Repr_addAppParen(v___x_928_, v___x_810_);
v___x_930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_925_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_817_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_924_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_820_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_822_);
v___x_935_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_807_);
v___x_938_ = l_String_quote(v_leantar_795_);
v___x_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_811_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Repr_addAppParen(v___x_940_, v___x_810_);
v___x_942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_809_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_817_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_937_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_820_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_822_);
v___x_947_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_807_);
v___x_950_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_951_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_sharedDynlibs_796_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_817_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_949_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_820_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_822_);
v___x_957_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_807_);
v___x_960_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_797_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_875_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_817_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_820_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_822_);
v___x_966_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_807_);
v___x_969_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__27, &l_Lake_instReprLeanInstall_repr___redArg___closed__27_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27);
v___x_970_ = l_String_quote(v_ar_798_);
v___x_971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_811_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Repr_addAppParen(v___x_972_, v___x_810_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_969_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_817_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_968_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_820_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_822_);
v___x_979_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__28));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_807_);
v___x_982_ = l_String_quote(v_cc_799_);
v___x_983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_811_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Repr_addAppParen(v___x_984_, v___x_810_);
v___x_986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_969_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*1, v___x_817_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_981_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_820_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_822_);
v___x_991_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_807_);
v___x_994_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__31, &l_Lake_instReprLeanInstall_repr___redArg___closed__31_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31);
v___x_995_ = l_Bool_repr___redArg(v_customCc_800_);
v___x_996_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*1, v___x_817_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_993_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_820_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_822_);
v___x_1001_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__33));
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_807_);
v___x_1004_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_cFlags_801_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_837_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_817_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1003_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_820_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_822_);
v___x_1010_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__35));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_807_);
v___x_1013_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__36, &l_Lake_instReprLeanInstall_repr___redArg___closed__36_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36);
v___x_1014_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkStaticFlags_802_);
v___x_1015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*1, v___x_817_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1012_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_820_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_822_);
v___x_1020_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__38));
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_807_);
v___x_1023_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkSharedFlags_803_);
v___x_1024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1013_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*1, v___x_817_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1022_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_820_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_822_);
v___x_1029_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__40));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_807_);
v___x_1032_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccFlags_804_);
v___x_1033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_809_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*1, v___x_817_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1031_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_820_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_822_);
v___x_1038_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__42));
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_807_);
v___x_1041_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__43, &l_Lake_instReprLeanInstall_repr___redArg___closed__43_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43);
v___x_1042_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkStaticFlags_805_);
v___x_1043_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*1, v___x_817_);
v___x_1045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1040_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_820_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_822_);
v___x_1048_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__45));
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_807_);
v___x_1051_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkSharedFlags_806_);
v___x_1052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1041_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*1, v___x_817_);
v___x_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1050_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1056_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1054_);
v___x_1058_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1055_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*1, v___x_817_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_1062_, lean_object* v_prec_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_1065_, lean_object* v_prec_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lake_instReprLeanInstall_repr(v_x_1065_, v_prec_1066_);
lean_dec(v_prec_1066_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib(lean_object* v_self_1070_){
_start:
{
lean_object* v_sharedDynlib_1071_; lean_object* v_path_1072_; 
v_sharedDynlib_1071_ = lean_ctor_get(v_self_1070_, 12);
v_path_1072_ = lean_ctor_get(v_sharedDynlib_1071_, 0);
lean_inc_ref(v_path_1072_);
return v_path_1072_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib___boxed(lean_object* v_self_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lake_LeanInstall_sharedLib(v_self_1073_);
lean_dec_ref(v_self_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_initSharedLib(lean_object* v_self_1075_){
_start:
{
lean_object* v_sysroot_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_sysroot_1076_ = lean_ctor_get(v_self_1075_, 0);
lean_inc_ref(v_sysroot_1076_);
lean_dec_ref(v_self_1075_);
v___x_1077_ = l_Lake_leanSharedLibDir(v_sysroot_1076_);
v___x_1078_ = l_Lake_initSharedLib;
v___x_1079_ = l_System_FilePath_join(v___x_1077_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_1080_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = l_System_Platform_isWindows;
if (v___x_1081_ == 0)
{
lean_object* v_leanLibDir_1082_; lean_object* v_systemLibDir_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_leanLibDir_1082_ = lean_ctor_get(v_self_1080_, 3);
v_systemLibDir_1083_ = lean_ctor_get(v_self_1080_, 5);
v___x_1084_ = lean_box(0);
lean_inc_ref(v_systemLibDir_1083_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_systemLibDir_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
lean_inc_ref(v_leanLibDir_1082_);
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_leanLibDir_1082_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_binDir_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_binDir_1087_ = lean_ctor_get(v_self_1080_, 6);
v___x_1088_ = lean_box(0);
lean_inc_ref(v_binDir_1087_);
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_binDir_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lake_LeanInstall_sharedLibPath(v_self_1090_);
lean_dec_ref(v_self_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_1092_){
_start:
{
uint8_t v_customCc_1093_; 
v_customCc_1093_ = lean_ctor_get_uint8(v_self_1092_, sizeof(void*)*21);
if (v_customCc_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v_cc_1095_; lean_object* v___x_1096_; 
v_cc_1095_ = lean_ctor_get(v_self_1092_, 14);
lean_inc_ref(v_cc_1095_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_cc_1095_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lake_LeanInstall_leanCc_x3f(v_self_1097_);
lean_dec_ref(v_self_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_1099_, lean_object* v_self_1100_){
_start:
{
if (v_shared_1099_ == 0)
{
lean_object* v_ccLinkStaticFlags_1101_; 
v_ccLinkStaticFlags_1101_ = lean_ctor_get(v_self_1100_, 19);
lean_inc_ref(v_ccLinkStaticFlags_1101_);
return v_ccLinkStaticFlags_1101_;
}
else
{
lean_object* v_ccLinkSharedFlags_1102_; 
v_ccLinkSharedFlags_1102_ = lean_ctor_get(v_self_1100_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1102_);
return v_ccLinkSharedFlags_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_1103_, lean_object* v_self_1104_){
_start:
{
uint8_t v_shared_boxed_1105_; lean_object* v_res_1106_; 
v_shared_boxed_1105_ = lean_unbox(v_shared_1103_);
v_res_1106_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_1105_, v_self_1104_);
lean_dec_ref(v_self_1104_);
return v_res_1106_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = l_System_FilePath_exeExtension;
v___x_1109_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1110_ = l_System_FilePath_addExtension(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_1111_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = l_Lake_defaultBuildDir;
v___x_1113_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1114_ = l_System_FilePath_join(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__1(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = l_Lake_defaultBinDir;
v___x_1116_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1117_ = l_System_FilePath_join(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__2(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = l_Lake_defaultLeanLibDir;
v___x_1119_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1120_ = l_System_FilePath_join(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__4(void){
_start:
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = 0;
v___x_1123_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1124_ = l_Lake_nameToSharedLib(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__5(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
v___x_1126_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1127_ = l_System_FilePath_join(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__6(void){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1129_ = 0;
v___x_1130_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1131_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__5, &l_Lake_instInhabitedLakeInstall_default___closed__5_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__5);
v___x_1132_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1130_);
lean_ctor_set(v___x_1132_, 2, v___x_1128_);
lean_ctor_set(v___x_1132_, 3, v___x_1128_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*4, v___x_1129_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__7(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = l_Lake_lakeExe;
v___x_1134_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1135_ = l_System_FilePath_join(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__8(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1136_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__7, &l_Lake_instInhabitedLakeInstall_default___closed__7_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__7);
v___x_1137_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__6, &l_Lake_instInhabitedLakeInstall_default___closed__6_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__6);
v___x_1138_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1139_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1140_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1141_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
lean_ctor_set(v___x_1141_, 2, v___x_1139_);
lean_ctor_set(v___x_1141_, 3, v___x_1138_);
lean_ctor_set(v___x_1141_, 4, v___x_1137_);
lean_ctor_set(v___x_1141_, 5, v___x_1136_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__8, &l_Lake_instInhabitedLakeInstall_default___closed__8_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__8);
return v___x_1142_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_1149_){
_start:
{
lean_object* v_home_1150_; lean_object* v_srcDir_1151_; lean_object* v_binDir_1152_; lean_object* v_libDir_1153_; lean_object* v_sharedDynlib_1154_; lean_object* v_lake_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_home_1150_ = lean_ctor_get(v_x_1149_, 0);
lean_inc_ref(v_home_1150_);
v_srcDir_1151_ = lean_ctor_get(v_x_1149_, 1);
lean_inc_ref(v_srcDir_1151_);
v_binDir_1152_ = lean_ctor_get(v_x_1149_, 2);
lean_inc_ref(v_binDir_1152_);
v_libDir_1153_ = lean_ctor_get(v_x_1149_, 3);
lean_inc_ref(v_libDir_1153_);
v_sharedDynlib_1154_ = lean_ctor_get(v_x_1149_, 4);
lean_inc_ref(v_sharedDynlib_1154_);
v_lake_1155_ = lean_ctor_get(v_x_1149_, 5);
lean_inc_ref(v_lake_1155_);
lean_dec_ref(v_x_1149_);
v___x_1156_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_1157_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_1158_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_1161_ = l_String_quote(v_home_1150_);
v___x_1162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Repr_addAppParen(v___x_1163_, v___x_1159_);
v___x_1165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1158_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = 0;
v___x_1167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*1, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1157_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_1170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_box(1);
v___x_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v___x_1156_);
v___x_1176_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_1177_ = l_String_quote(v_srcDir_1151_);
v___x_1178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1160_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Repr_addAppParen(v___x_1179_, v___x_1159_);
v___x_1181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1176_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*1, v___x_1166_);
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1175_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1169_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1171_);
v___x_1186_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___x_1156_);
v___x_1189_ = l_String_quote(v_binDir_1152_);
v___x_1190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1160_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Repr_addAppParen(v___x_1191_, v___x_1159_);
v___x_1193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1176_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*1, v___x_1166_);
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1188_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1169_);
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1171_);
v___x_1198_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1156_);
v___x_1201_ = l_String_quote(v_libDir_1153_);
v___x_1202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1160_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Repr_addAppParen(v___x_1203_, v___x_1159_);
v___x_1205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1176_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*1, v___x_1166_);
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1200_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1169_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1171_);
v___x_1210_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1156_);
v___x_1213_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_1214_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_1154_);
v___x_1215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*1, v___x_1166_);
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1212_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1169_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1171_);
v___x_1220_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__2));
v___x_1221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1156_);
v___x_1223_ = l_String_quote(v_lake_1155_);
v___x_1224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1160_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = l_Repr_addAppParen(v___x_1225_, v___x_1159_);
v___x_1227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1158_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*1, v___x_1166_);
v___x_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1222_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1231_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1229_);
v___x_1233_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1230_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*1, v___x_1166_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_1237_, lean_object* v_prec_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_1240_, lean_object* v_prec_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lake_instReprLakeInstall_repr(v_x_1240_, v_prec_1241_);
lean_dec(v_prec_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_1245_){
_start:
{
lean_object* v_sharedDynlib_1246_; lean_object* v_path_1247_; 
v_sharedDynlib_1246_ = lean_ctor_get(v_self_1245_, 4);
v_path_1247_ = lean_ctor_get(v_sharedDynlib_1246_, 0);
lean_inc_ref(v_path_1247_);
return v_path_1247_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lake_LakeInstall_sharedLib(v_self_1248_);
lean_dec_ref(v_self_1248_);
return v_res_1249_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__2(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = l_Lake_sharedLibExt;
v___x_1253_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1254_ = lean_string_append(v___x_1253_, v___x_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_1256_){
_start:
{
lean_object* v_sysroot_1257_; lean_object* v_srcDir_1258_; lean_object* v_leanLibDir_1259_; lean_object* v_binDir_1260_; lean_object* v_sharedDynlibs_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___y_1265_; uint8_t v___x_1273_; 
v_sysroot_1257_ = lean_ctor_get(v_lean_1256_, 0);
lean_inc_ref(v_sysroot_1257_);
v_srcDir_1258_ = lean_ctor_get(v_lean_1256_, 2);
lean_inc_ref(v_srcDir_1258_);
v_leanLibDir_1259_ = lean_ctor_get(v_lean_1256_, 3);
lean_inc_ref(v_leanLibDir_1259_);
v_binDir_1260_ = lean_ctor_get(v_lean_1256_, 6);
lean_inc_ref(v_binDir_1260_);
v_sharedDynlibs_1261_ = lean_ctor_get(v_lean_1256_, 11);
lean_inc_ref(v_sharedDynlibs_1261_);
lean_dec_ref(v_lean_1256_);
v___x_1262_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1263_ = l_System_FilePath_join(v_srcDir_1258_, v___x_1262_);
v___x_1273_ = l_System_Platform_isWindows;
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__2, &l_Lake_LakeInstall_ofLean___closed__2_once, _init_l_Lake_LakeInstall_ofLean___closed__2);
lean_inc_ref(v_leanLibDir_1259_);
v___x_1275_ = l_System_FilePath_join(v_leanLibDir_1259_, v___x_1274_);
v___y_1265_ = v___x_1275_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__3));
lean_inc_ref(v_binDir_1260_);
v___x_1277_ = l_System_FilePath_join(v_binDir_1260_, v___x_1276_);
v___y_1265_ = v___x_1277_;
goto v___jp_1264_;
}
v___jp_1264_:
{
lean_object* v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1266_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_1267_ = 0;
v___x_1268_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1269_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1269_, 0, v___y_1265_);
lean_ctor_set(v___x_1269_, 1, v___x_1266_);
lean_ctor_set(v___x_1269_, 2, v_sharedDynlibs_1261_);
lean_ctor_set(v___x_1269_, 3, v___x_1268_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*4, v___x_1267_);
v___x_1270_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_1260_);
v___x_1271_ = l_System_FilePath_join(v_binDir_1260_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1272_, 0, v_sysroot_1257_);
lean_ctor_set(v___x_1272_, 1, v___x_1263_);
lean_ctor_set(v___x_1272_, 2, v_binDir_1260_);
lean_ctor_set(v___x_1272_, 3, v_leanLibDir_1259_);
lean_ctor_set(v___x_1272_, 4, v___x_1269_);
lean_ctor_set(v___x_1272_, 5, v___x_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_1282_ = lean_io_getenv(v___x_1281_);
if (lean_obj_tag(v___x_1282_) == 1)
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1310_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1310_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1310_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___y_1290_; 
v___x_1287_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_1288_ = lean_io_getenv(v___x_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_1290_ = v___x_1308_;
goto v___jp_1289_;
}
else
{
lean_object* v_val_1309_; 
v_val_1309_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v___x_1288_, 1);
v___y_1290_ = v_val_1309_;
goto v___jp_1289_;
}
v___jp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_startInclusive_1295_; lean_object* v_endExclusive_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_string_utf8_byte_size(v___y_1290_);
lean_inc_ref(v___y_1290_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___y_1290_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = l_String_Slice_trimAscii(v___x_1293_);
v_startInclusive_1295_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_startInclusive_1295_);
v_endExclusive_1296_ = lean_ctor_get(v___x_1294_, 2);
lean_inc(v_endExclusive_1296_);
lean_dec_ref(v___x_1294_);
v___x_1297_ = lean_nat_sub(v_endExclusive_1296_, v_startInclusive_1295_);
lean_dec(v_startInclusive_1295_);
lean_dec(v_endExclusive_1296_);
v___x_1298_ = lean_nat_dec_eq(v___x_1297_, v___x_1291_);
lean_dec(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1299_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
lean_inc_n(v_val_1283_, 2);
v___x_1300_ = l_System_FilePath_join(v_val_1283_, v___x_1299_);
v___x_1301_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_1302_ = l_System_FilePath_join(v_val_1283_, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1303_, 0, v_val_1283_);
lean_ctor_set(v___x_1303_, 1, v___y_1290_);
lean_ctor_set(v___x_1303_, 2, v___x_1300_);
lean_ctor_set(v___x_1303_, 3, v___x_1302_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1303_);
v___x_1305_ = v___x_1285_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
else
{
lean_object* v___x_1307_; 
lean_dec_ref(v___y_1290_);
lean_del_object(v___x_1285_);
lean_dec(v_val_1283_);
v___x_1307_ = lean_box(0);
return v___x_1307_;
}
}
}
}
else
{
lean_object* v___x_1311_; 
lean_dec(v___x_1282_);
v___x_1311_ = lean_box(0);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lake_findElanInstall_x3f();
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1325_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1326_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1330_ = 1;
v___x_1331_ = 0;
v___x_1332_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1332_, 0, v___x_1325_);
lean_ctor_set(v___x_1332_, 1, v_lean_1323_);
lean_ctor_set(v___x_1332_, 2, v___x_1326_);
lean_ctor_set(v___x_1332_, 3, v___x_1327_);
lean_ctor_set(v___x_1332_, 4, v___x_1329_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*5, v___x_1330_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*5 + 1, v___x_1331_);
v___x_1333_ = l_IO_Process_output(v___x_1332_, v___x_1327_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1352_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1352_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1352_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
uint32_t v_exitCode_1338_; lean_object* v_stdout_1339_; uint32_t v___x_1340_; uint8_t v___x_1341_; 
v_exitCode_1338_ = lean_ctor_get_uint32(v_a_1334_, sizeof(void*)*2);
v_stdout_1339_ = lean_ctor_get(v_a_1334_, 0);
lean_inc_ref(v_stdout_1339_);
lean_dec(v_a_1334_);
v___x_1340_ = 0;
v___x_1341_ = lean_uint32_dec_eq(v_exitCode_1338_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v_stdout_1339_);
lean_del_object(v___x_1336_);
return v___x_1327_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_str_1345_; lean_object* v_startInclusive_1346_; lean_object* v_endExclusive_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1342_ = lean_string_utf8_byte_size(v_stdout_1339_);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v_stdout_1339_);
lean_ctor_set(v___x_1343_, 1, v___x_1328_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
v___x_1344_ = l_String_Slice_trimAscii(v___x_1343_);
v_str_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc_ref(v_str_1345_);
v_startInclusive_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_startInclusive_1346_);
v_endExclusive_1347_ = lean_ctor_get(v___x_1344_, 2);
lean_inc(v_endExclusive_1347_);
lean_dec_ref(v___x_1344_);
v___x_1348_ = lean_string_utf8_extract_fast(v_str_1345_, v_startInclusive_1346_, v_endExclusive_1347_);
lean_dec(v_endExclusive_1347_);
lean_dec(v_startInclusive_1346_);
lean_dec_ref(v_str_1345_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1348_);
v___x_1350_ = v___x_1336_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1333_, 1);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lake_findLeanSysroot_x3f(v_lean_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1363_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1364_ = l_Lake_leanExe(v_sysroot_1361_);
v___x_1365_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1369_ = 1;
v___x_1370_ = 0;
v___x_1371_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1371_, 0, v___x_1363_);
lean_ctor_set(v___x_1371_, 1, v___x_1364_);
lean_ctor_set(v___x_1371_, 2, v___x_1365_);
lean_ctor_set(v___x_1371_, 3, v___x_1366_);
lean_ctor_set(v___x_1371_, 4, v___x_1368_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5, v___x_1369_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5 + 1, v___x_1370_);
v___x_1372_ = l_IO_Process_output(v___x_1371_, v___x_1366_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v_stdout_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_str_1378_; lean_object* v_startInclusive_1379_; lean_object* v_endExclusive_1380_; lean_object* v___x_1381_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v_stdout_1374_ = lean_ctor_get(v_a_1373_, 0);
lean_inc_ref(v_stdout_1374_);
lean_dec(v_a_1373_);
v___x_1375_ = lean_string_utf8_byte_size(v_stdout_1374_);
v___x_1376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1376_, 0, v_stdout_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1367_);
lean_ctor_set(v___x_1376_, 2, v___x_1375_);
v___x_1377_ = l_String_Slice_trimAscii(v___x_1376_);
v_str_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_str_1378_);
v_startInclusive_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_startInclusive_1379_);
v_endExclusive_1380_ = lean_ctor_get(v___x_1377_, 2);
lean_inc(v_endExclusive_1380_);
lean_dec_ref(v___x_1377_);
v___x_1381_ = lean_string_utf8_extract_fast(v_str_1378_, v_startInclusive_1379_, v_endExclusive_1380_);
lean_dec(v_endExclusive_1380_);
lean_dec(v_startInclusive_1379_);
lean_dec_ref(v_str_1378_);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; 
lean_dec_ref_known(v___x_1372_, 1);
v___x_1382_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1391_ = lean_io_getenv(v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 1)
{
lean_object* v_val_1392_; 
lean_dec_ref(v_sysroot_1388_);
v_val_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v___x_1391_, 1);
return v_val_1392_;
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
lean_dec(v___x_1391_);
v___x_1393_ = l_Lake_leanArExe(v_sysroot_1388_);
v___x_1394_ = l_System_FilePath_pathExists(v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1393_);
v___x_1395_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1396_ = lean_io_getenv(v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 1)
{
lean_object* v_val_1397_; 
v_val_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_val_1397_);
lean_dec_ref_known(v___x_1396_, 1);
return v_val_1397_;
}
else
{
lean_object* v___x_1398_; 
lean_dec(v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
return v___x_1398_;
}
}
else
{
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1402_, lean_object* v_i_1403_, lean_object* v_cc_1404_){
_start:
{
lean_object* v_sysroot_1405_; lean_object* v_githash_1406_; lean_object* v_srcDir_1407_; lean_object* v_leanLibDir_1408_; lean_object* v_includeDir_1409_; lean_object* v_systemLibDir_1410_; lean_object* v_binDir_1411_; lean_object* v_lean_1412_; lean_object* v_leanir_1413_; lean_object* v_leanc_1414_; lean_object* v_leantar_1415_; lean_object* v_sharedDynlibs_1416_; lean_object* v_sharedDynlib_1417_; lean_object* v_ar_1418_; lean_object* v_cFlags_1419_; lean_object* v_linkStaticFlags_1420_; lean_object* v_linkSharedFlags_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1434_; 
v_sysroot_1405_ = lean_ctor_get(v_i_1403_, 0);
v_githash_1406_ = lean_ctor_get(v_i_1403_, 1);
v_srcDir_1407_ = lean_ctor_get(v_i_1403_, 2);
v_leanLibDir_1408_ = lean_ctor_get(v_i_1403_, 3);
v_includeDir_1409_ = lean_ctor_get(v_i_1403_, 4);
v_systemLibDir_1410_ = lean_ctor_get(v_i_1403_, 5);
v_binDir_1411_ = lean_ctor_get(v_i_1403_, 6);
v_lean_1412_ = lean_ctor_get(v_i_1403_, 7);
v_leanir_1413_ = lean_ctor_get(v_i_1403_, 8);
v_leanc_1414_ = lean_ctor_get(v_i_1403_, 9);
v_leantar_1415_ = lean_ctor_get(v_i_1403_, 10);
v_sharedDynlibs_1416_ = lean_ctor_get(v_i_1403_, 11);
v_sharedDynlib_1417_ = lean_ctor_get(v_i_1403_, 12);
v_ar_1418_ = lean_ctor_get(v_i_1403_, 13);
v_cFlags_1419_ = lean_ctor_get(v_i_1403_, 15);
v_linkStaticFlags_1420_ = lean_ctor_get(v_i_1403_, 16);
v_linkSharedFlags_1421_ = lean_ctor_get(v_i_1403_, 17);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_i_1403_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; 
v_unused_1435_ = lean_ctor_get(v_i_1403_, 20);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_i_1403_, 19);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_i_1403_, 18);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_i_1403_, 14);
lean_dec(v_unused_1438_);
v___x_1423_ = v_i_1403_;
v_isShared_1424_ = v_isSharedCheck_1434_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_linkSharedFlags_1421_);
lean_inc(v_linkStaticFlags_1420_);
lean_inc(v_cFlags_1419_);
lean_inc(v_ar_1418_);
lean_inc(v_sharedDynlib_1417_);
lean_inc(v_sharedDynlibs_1416_);
lean_inc(v_leantar_1415_);
lean_inc(v_leanc_1414_);
lean_inc(v_leanir_1413_);
lean_inc(v_lean_1412_);
lean_inc(v_binDir_1411_);
lean_inc(v_systemLibDir_1410_);
lean_inc(v_includeDir_1409_);
lean_inc(v_leanLibDir_1408_);
lean_inc(v_srcDir_1407_);
lean_inc(v_githash_1406_);
lean_inc(v_sysroot_1405_);
lean_dec(v_i_1403_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1434_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_ccLinkFlags_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v_ccLinkFlags_1425_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1402_);
v___x_1426_ = 0;
v___x_1427_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1402_);
lean_inc_ref(v_cFlags_1419_);
v___x_1428_ = l_Array_append___redArg(v_cFlags_1419_, v___x_1427_);
lean_dec_ref(v___x_1427_);
lean_inc_ref(v_ccLinkFlags_1425_);
v___x_1429_ = l_Array_append___redArg(v_ccLinkFlags_1425_, v_linkStaticFlags_1420_);
v___x_1430_ = l_Array_append___redArg(v_ccLinkFlags_1425_, v_linkSharedFlags_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 20, v___x_1430_);
lean_ctor_set(v___x_1423_, 19, v___x_1429_);
lean_ctor_set(v___x_1423_, 18, v___x_1428_);
lean_ctor_set(v___x_1423_, 14, v_cc_1404_);
v___x_1432_ = v___x_1423_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_sysroot_1405_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_githash_1406_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_srcDir_1407_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v_leanLibDir_1408_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_includeDir_1409_);
lean_ctor_set(v_reuseFailAlloc_1433_, 5, v_systemLibDir_1410_);
lean_ctor_set(v_reuseFailAlloc_1433_, 6, v_binDir_1411_);
lean_ctor_set(v_reuseFailAlloc_1433_, 7, v_lean_1412_);
lean_ctor_set(v_reuseFailAlloc_1433_, 8, v_leanir_1413_);
lean_ctor_set(v_reuseFailAlloc_1433_, 9, v_leanc_1414_);
lean_ctor_set(v_reuseFailAlloc_1433_, 10, v_leantar_1415_);
lean_ctor_set(v_reuseFailAlloc_1433_, 11, v_sharedDynlibs_1416_);
lean_ctor_set(v_reuseFailAlloc_1433_, 12, v_sharedDynlib_1417_);
lean_ctor_set(v_reuseFailAlloc_1433_, 13, v_ar_1418_);
lean_ctor_set(v_reuseFailAlloc_1433_, 14, v_cc_1404_);
lean_ctor_set(v_reuseFailAlloc_1433_, 15, v_cFlags_1419_);
lean_ctor_set(v_reuseFailAlloc_1433_, 16, v_linkStaticFlags_1420_);
lean_ctor_set(v_reuseFailAlloc_1433_, 17, v_linkSharedFlags_1421_);
lean_ctor_set(v_reuseFailAlloc_1433_, 18, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1433_, 19, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1433_, 20, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*21, v___x_1426_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1439_, lean_object* v_i_1440_, lean_object* v_cc_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1439_, v_i_1440_, v_cc_1441_);
lean_dec_ref(v_sysroot_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1443_, lean_object* v_cc_1444_){
_start:
{
lean_object* v_sysroot_1445_; lean_object* v_githash_1446_; lean_object* v_srcDir_1447_; lean_object* v_leanLibDir_1448_; lean_object* v_includeDir_1449_; lean_object* v_systemLibDir_1450_; lean_object* v_binDir_1451_; lean_object* v_lean_1452_; lean_object* v_leanir_1453_; lean_object* v_leanc_1454_; lean_object* v_leantar_1455_; lean_object* v_sharedDynlibs_1456_; lean_object* v_sharedDynlib_1457_; lean_object* v_ar_1458_; uint8_t v_customCc_1459_; lean_object* v_cFlags_1460_; lean_object* v_linkStaticFlags_1461_; lean_object* v_linkSharedFlags_1462_; lean_object* v_ccFlags_1463_; lean_object* v_ccLinkStaticFlags_1464_; lean_object* v_ccLinkSharedFlags_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_sysroot_1445_ = lean_ctor_get(v_i_1443_, 0);
v_githash_1446_ = lean_ctor_get(v_i_1443_, 1);
v_srcDir_1447_ = lean_ctor_get(v_i_1443_, 2);
v_leanLibDir_1448_ = lean_ctor_get(v_i_1443_, 3);
v_includeDir_1449_ = lean_ctor_get(v_i_1443_, 4);
v_systemLibDir_1450_ = lean_ctor_get(v_i_1443_, 5);
v_binDir_1451_ = lean_ctor_get(v_i_1443_, 6);
v_lean_1452_ = lean_ctor_get(v_i_1443_, 7);
v_leanir_1453_ = lean_ctor_get(v_i_1443_, 8);
v_leanc_1454_ = lean_ctor_get(v_i_1443_, 9);
v_leantar_1455_ = lean_ctor_get(v_i_1443_, 10);
v_sharedDynlibs_1456_ = lean_ctor_get(v_i_1443_, 11);
v_sharedDynlib_1457_ = lean_ctor_get(v_i_1443_, 12);
v_ar_1458_ = lean_ctor_get(v_i_1443_, 13);
v_customCc_1459_ = lean_ctor_get_uint8(v_i_1443_, sizeof(void*)*21);
v_cFlags_1460_ = lean_ctor_get(v_i_1443_, 15);
v_linkStaticFlags_1461_ = lean_ctor_get(v_i_1443_, 16);
v_linkSharedFlags_1462_ = lean_ctor_get(v_i_1443_, 17);
v_ccFlags_1463_ = lean_ctor_get(v_i_1443_, 18);
v_ccLinkStaticFlags_1464_ = lean_ctor_get(v_i_1443_, 19);
v_ccLinkSharedFlags_1465_ = lean_ctor_get(v_i_1443_, 20);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_i_1443_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_i_1443_, 14);
lean_dec(v_unused_1473_);
v___x_1467_ = v_i_1443_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1465_);
lean_inc(v_ccLinkStaticFlags_1464_);
lean_inc(v_ccFlags_1463_);
lean_inc(v_linkSharedFlags_1462_);
lean_inc(v_linkStaticFlags_1461_);
lean_inc(v_cFlags_1460_);
lean_inc(v_ar_1458_);
lean_inc(v_sharedDynlib_1457_);
lean_inc(v_sharedDynlibs_1456_);
lean_inc(v_leantar_1455_);
lean_inc(v_leanc_1454_);
lean_inc(v_leanir_1453_);
lean_inc(v_lean_1452_);
lean_inc(v_binDir_1451_);
lean_inc(v_systemLibDir_1450_);
lean_inc(v_includeDir_1449_);
lean_inc(v_leanLibDir_1448_);
lean_inc(v_srcDir_1447_);
lean_inc(v_githash_1446_);
lean_inc(v_sysroot_1445_);
lean_dec(v_i_1443_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 14, v_cc_1444_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_sysroot_1445_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_githash_1446_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_srcDir_1447_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_leanLibDir_1448_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v_includeDir_1449_);
lean_ctor_set(v_reuseFailAlloc_1471_, 5, v_systemLibDir_1450_);
lean_ctor_set(v_reuseFailAlloc_1471_, 6, v_binDir_1451_);
lean_ctor_set(v_reuseFailAlloc_1471_, 7, v_lean_1452_);
lean_ctor_set(v_reuseFailAlloc_1471_, 8, v_leanir_1453_);
lean_ctor_set(v_reuseFailAlloc_1471_, 9, v_leanc_1454_);
lean_ctor_set(v_reuseFailAlloc_1471_, 10, v_leantar_1455_);
lean_ctor_set(v_reuseFailAlloc_1471_, 11, v_sharedDynlibs_1456_);
lean_ctor_set(v_reuseFailAlloc_1471_, 12, v_sharedDynlib_1457_);
lean_ctor_set(v_reuseFailAlloc_1471_, 13, v_ar_1458_);
lean_ctor_set(v_reuseFailAlloc_1471_, 14, v_cc_1444_);
lean_ctor_set(v_reuseFailAlloc_1471_, 15, v_cFlags_1460_);
lean_ctor_set(v_reuseFailAlloc_1471_, 16, v_linkStaticFlags_1461_);
lean_ctor_set(v_reuseFailAlloc_1471_, 17, v_linkSharedFlags_1462_);
lean_ctor_set(v_reuseFailAlloc_1471_, 18, v_ccFlags_1463_);
lean_ctor_set(v_reuseFailAlloc_1471_, 19, v_ccLinkStaticFlags_1464_);
lean_ctor_set(v_reuseFailAlloc_1471_, 20, v_ccLinkSharedFlags_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*21, v_customCc_1459_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1476_, lean_object* v_i_1477_){
_start:
{
lean_object* v_cc_1480_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1511_ = lean_io_getenv(v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 1)
{
lean_object* v_val_1512_; 
lean_dec_ref(v_sysroot_1476_);
v_val_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_val_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v_cc_1480_ = v_val_1512_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
lean_dec(v___x_1511_);
lean_inc_ref(v_sysroot_1476_);
v___x_1513_ = l_Lake_leanCcExe(v_sysroot_1476_);
v___x_1514_ = l_System_FilePath_pathExists(v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_sysroot_1476_);
v___x_1515_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1516_ = lean_io_getenv(v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_object* v_val_1517_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v_cc_1480_ = v_val_1517_;
goto v___jp_1479_;
}
else
{
lean_object* v_sysroot_1518_; lean_object* v_githash_1519_; lean_object* v_srcDir_1520_; lean_object* v_leanLibDir_1521_; lean_object* v_includeDir_1522_; lean_object* v_systemLibDir_1523_; lean_object* v_binDir_1524_; lean_object* v_lean_1525_; lean_object* v_leanir_1526_; lean_object* v_leanc_1527_; lean_object* v_leantar_1528_; lean_object* v_sharedDynlibs_1529_; lean_object* v_sharedDynlib_1530_; lean_object* v_ar_1531_; uint8_t v_customCc_1532_; lean_object* v_cFlags_1533_; lean_object* v_linkStaticFlags_1534_; lean_object* v_linkSharedFlags_1535_; lean_object* v_ccFlags_1536_; lean_object* v_ccLinkStaticFlags_1537_; lean_object* v_ccLinkSharedFlags_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v___x_1516_);
v_sysroot_1518_ = lean_ctor_get(v_i_1477_, 0);
v_githash_1519_ = lean_ctor_get(v_i_1477_, 1);
v_srcDir_1520_ = lean_ctor_get(v_i_1477_, 2);
v_leanLibDir_1521_ = lean_ctor_get(v_i_1477_, 3);
v_includeDir_1522_ = lean_ctor_get(v_i_1477_, 4);
v_systemLibDir_1523_ = lean_ctor_get(v_i_1477_, 5);
v_binDir_1524_ = lean_ctor_get(v_i_1477_, 6);
v_lean_1525_ = lean_ctor_get(v_i_1477_, 7);
v_leanir_1526_ = lean_ctor_get(v_i_1477_, 8);
v_leanc_1527_ = lean_ctor_get(v_i_1477_, 9);
v_leantar_1528_ = lean_ctor_get(v_i_1477_, 10);
v_sharedDynlibs_1529_ = lean_ctor_get(v_i_1477_, 11);
v_sharedDynlib_1530_ = lean_ctor_get(v_i_1477_, 12);
v_ar_1531_ = lean_ctor_get(v_i_1477_, 13);
v_customCc_1532_ = lean_ctor_get_uint8(v_i_1477_, sizeof(void*)*21);
v_cFlags_1533_ = lean_ctor_get(v_i_1477_, 15);
v_linkStaticFlags_1534_ = lean_ctor_get(v_i_1477_, 16);
v_linkSharedFlags_1535_ = lean_ctor_get(v_i_1477_, 17);
v_ccFlags_1536_ = lean_ctor_get(v_i_1477_, 18);
v_ccLinkStaticFlags_1537_ = lean_ctor_get(v_i_1477_, 19);
v_ccLinkSharedFlags_1538_ = lean_ctor_get(v_i_1477_, 20);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_i_1477_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_i_1477_, 14);
lean_dec(v_unused_1547_);
v___x_1540_ = v_i_1477_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1538_);
lean_inc(v_ccLinkStaticFlags_1537_);
lean_inc(v_ccFlags_1536_);
lean_inc(v_linkSharedFlags_1535_);
lean_inc(v_linkStaticFlags_1534_);
lean_inc(v_cFlags_1533_);
lean_inc(v_ar_1531_);
lean_inc(v_sharedDynlib_1530_);
lean_inc(v_sharedDynlibs_1529_);
lean_inc(v_leantar_1528_);
lean_inc(v_leanc_1527_);
lean_inc(v_leanir_1526_);
lean_inc(v_lean_1525_);
lean_inc(v_binDir_1524_);
lean_inc(v_systemLibDir_1523_);
lean_inc(v_includeDir_1522_);
lean_inc(v_leanLibDir_1521_);
lean_inc(v_srcDir_1520_);
lean_inc(v_githash_1519_);
lean_inc(v_sysroot_1518_);
lean_dec(v_i_1477_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 14, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_sysroot_1518_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_githash_1519_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_srcDir_1520_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_leanLibDir_1521_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_includeDir_1522_);
lean_ctor_set(v_reuseFailAlloc_1545_, 5, v_systemLibDir_1523_);
lean_ctor_set(v_reuseFailAlloc_1545_, 6, v_binDir_1524_);
lean_ctor_set(v_reuseFailAlloc_1545_, 7, v_lean_1525_);
lean_ctor_set(v_reuseFailAlloc_1545_, 8, v_leanir_1526_);
lean_ctor_set(v_reuseFailAlloc_1545_, 9, v_leanc_1527_);
lean_ctor_set(v_reuseFailAlloc_1545_, 10, v_leantar_1528_);
lean_ctor_set(v_reuseFailAlloc_1545_, 11, v_sharedDynlibs_1529_);
lean_ctor_set(v_reuseFailAlloc_1545_, 12, v_sharedDynlib_1530_);
lean_ctor_set(v_reuseFailAlloc_1545_, 13, v_ar_1531_);
lean_ctor_set(v_reuseFailAlloc_1545_, 14, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 15, v_cFlags_1533_);
lean_ctor_set(v_reuseFailAlloc_1545_, 16, v_linkStaticFlags_1534_);
lean_ctor_set(v_reuseFailAlloc_1545_, 17, v_linkSharedFlags_1535_);
lean_ctor_set(v_reuseFailAlloc_1545_, 18, v_ccFlags_1536_);
lean_ctor_set(v_reuseFailAlloc_1545_, 19, v_ccLinkStaticFlags_1537_);
lean_ctor_set(v_reuseFailAlloc_1545_, 20, v_ccLinkSharedFlags_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*21, v_customCc_1532_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1476_, v_i_1477_, v___x_1513_);
lean_dec_ref(v_sysroot_1476_);
return v___x_1548_;
}
}
v___jp_1479_:
{
lean_object* v_sysroot_1481_; lean_object* v_githash_1482_; lean_object* v_srcDir_1483_; lean_object* v_leanLibDir_1484_; lean_object* v_includeDir_1485_; lean_object* v_systemLibDir_1486_; lean_object* v_binDir_1487_; lean_object* v_lean_1488_; lean_object* v_leanir_1489_; lean_object* v_leanc_1490_; lean_object* v_leantar_1491_; lean_object* v_sharedDynlibs_1492_; lean_object* v_sharedDynlib_1493_; lean_object* v_ar_1494_; uint8_t v_customCc_1495_; lean_object* v_cFlags_1496_; lean_object* v_linkStaticFlags_1497_; lean_object* v_linkSharedFlags_1498_; lean_object* v_ccFlags_1499_; lean_object* v_ccLinkStaticFlags_1500_; lean_object* v_ccLinkSharedFlags_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_sysroot_1481_ = lean_ctor_get(v_i_1477_, 0);
v_githash_1482_ = lean_ctor_get(v_i_1477_, 1);
v_srcDir_1483_ = lean_ctor_get(v_i_1477_, 2);
v_leanLibDir_1484_ = lean_ctor_get(v_i_1477_, 3);
v_includeDir_1485_ = lean_ctor_get(v_i_1477_, 4);
v_systemLibDir_1486_ = lean_ctor_get(v_i_1477_, 5);
v_binDir_1487_ = lean_ctor_get(v_i_1477_, 6);
v_lean_1488_ = lean_ctor_get(v_i_1477_, 7);
v_leanir_1489_ = lean_ctor_get(v_i_1477_, 8);
v_leanc_1490_ = lean_ctor_get(v_i_1477_, 9);
v_leantar_1491_ = lean_ctor_get(v_i_1477_, 10);
v_sharedDynlibs_1492_ = lean_ctor_get(v_i_1477_, 11);
v_sharedDynlib_1493_ = lean_ctor_get(v_i_1477_, 12);
v_ar_1494_ = lean_ctor_get(v_i_1477_, 13);
v_customCc_1495_ = lean_ctor_get_uint8(v_i_1477_, sizeof(void*)*21);
v_cFlags_1496_ = lean_ctor_get(v_i_1477_, 15);
v_linkStaticFlags_1497_ = lean_ctor_get(v_i_1477_, 16);
v_linkSharedFlags_1498_ = lean_ctor_get(v_i_1477_, 17);
v_ccFlags_1499_ = lean_ctor_get(v_i_1477_, 18);
v_ccLinkStaticFlags_1500_ = lean_ctor_get(v_i_1477_, 19);
v_ccLinkSharedFlags_1501_ = lean_ctor_get(v_i_1477_, 20);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_i_1477_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_i_1477_, 14);
lean_dec(v_unused_1509_);
v___x_1503_ = v_i_1477_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1501_);
lean_inc(v_ccLinkStaticFlags_1500_);
lean_inc(v_ccFlags_1499_);
lean_inc(v_linkSharedFlags_1498_);
lean_inc(v_linkStaticFlags_1497_);
lean_inc(v_cFlags_1496_);
lean_inc(v_ar_1494_);
lean_inc(v_sharedDynlib_1493_);
lean_inc(v_sharedDynlibs_1492_);
lean_inc(v_leantar_1491_);
lean_inc(v_leanc_1490_);
lean_inc(v_leanir_1489_);
lean_inc(v_lean_1488_);
lean_inc(v_binDir_1487_);
lean_inc(v_systemLibDir_1486_);
lean_inc(v_includeDir_1485_);
lean_inc(v_leanLibDir_1484_);
lean_inc(v_srcDir_1483_);
lean_inc(v_githash_1482_);
lean_inc(v_sysroot_1481_);
lean_dec(v_i_1477_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 14, v_cc_1480_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_sysroot_1481_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_githash_1482_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_srcDir_1483_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_leanLibDir_1484_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_includeDir_1485_);
lean_ctor_set(v_reuseFailAlloc_1507_, 5, v_systemLibDir_1486_);
lean_ctor_set(v_reuseFailAlloc_1507_, 6, v_binDir_1487_);
lean_ctor_set(v_reuseFailAlloc_1507_, 7, v_lean_1488_);
lean_ctor_set(v_reuseFailAlloc_1507_, 8, v_leanir_1489_);
lean_ctor_set(v_reuseFailAlloc_1507_, 9, v_leanc_1490_);
lean_ctor_set(v_reuseFailAlloc_1507_, 10, v_leantar_1491_);
lean_ctor_set(v_reuseFailAlloc_1507_, 11, v_sharedDynlibs_1492_);
lean_ctor_set(v_reuseFailAlloc_1507_, 12, v_sharedDynlib_1493_);
lean_ctor_set(v_reuseFailAlloc_1507_, 13, v_ar_1494_);
lean_ctor_set(v_reuseFailAlloc_1507_, 14, v_cc_1480_);
lean_ctor_set(v_reuseFailAlloc_1507_, 15, v_cFlags_1496_);
lean_ctor_set(v_reuseFailAlloc_1507_, 16, v_linkStaticFlags_1497_);
lean_ctor_set(v_reuseFailAlloc_1507_, 17, v_linkSharedFlags_1498_);
lean_ctor_set(v_reuseFailAlloc_1507_, 18, v_ccFlags_1499_);
lean_ctor_set(v_reuseFailAlloc_1507_, 19, v_ccLinkStaticFlags_1500_);
lean_ctor_set(v_reuseFailAlloc_1507_, 20, v_ccLinkSharedFlags_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1507_, sizeof(void*)*21, v_customCc_1495_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1549_, lean_object* v_i_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1549_, v_i_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1553_, uint8_t v_collocated_1554_){
_start:
{
lean_object* v_githash_1557_; 
if (v_collocated_1554_ == 0)
{
lean_object* v___x_1583_; 
lean_inc_ref(v_sysroot_1553_);
v___x_1583_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1553_);
v_githash_1557_ = v___x_1583_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_githash;
v_githash_1557_ = v___x_1584_;
goto v___jp_1556_;
}
v___jp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_inc_ref_n(v_sysroot_1553_, 12);
v___x_1558_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1553_);
v___x_1559_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1560_ = l_System_FilePath_join(v_sysroot_1553_, v___x_1559_);
v___x_1561_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1562_ = l_System_FilePath_join(v___x_1560_, v___x_1561_);
v___x_1563_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1564_ = l_System_FilePath_join(v_sysroot_1553_, v___x_1563_);
lean_inc_ref(v___x_1564_);
v___x_1565_ = l_System_FilePath_join(v___x_1564_, v___x_1561_);
v___x_1566_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1567_ = l_System_FilePath_join(v_sysroot_1553_, v___x_1566_);
v___x_1568_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1569_ = l_System_FilePath_join(v_sysroot_1553_, v___x_1568_);
v___x_1570_ = l_Lake_leanExe(v_sysroot_1553_);
v___x_1571_ = l_Lake_leanirExe(v_sysroot_1553_);
v___x_1572_ = l_Lake_leancExe(v_sysroot_1553_);
v___x_1573_ = l_Lake_leantarExe(v_sysroot_1553_);
v___x_1574_ = l_Lake_leanSharedDynlibs(v_sysroot_1553_);
v___x_1575_ = l_Lake_leanSharedDynlib(v_sysroot_1553_);
v___x_1576_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1577_ = 1;
v___x_1578_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1579_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1580_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_1581_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1581_, 0, v_sysroot_1553_);
lean_ctor_set(v___x_1581_, 1, v_githash_1557_);
lean_ctor_set(v___x_1581_, 2, v___x_1562_);
lean_ctor_set(v___x_1581_, 3, v___x_1565_);
lean_ctor_set(v___x_1581_, 4, v___x_1567_);
lean_ctor_set(v___x_1581_, 5, v___x_1564_);
lean_ctor_set(v___x_1581_, 6, v___x_1569_);
lean_ctor_set(v___x_1581_, 7, v___x_1570_);
lean_ctor_set(v___x_1581_, 8, v___x_1571_);
lean_ctor_set(v___x_1581_, 9, v___x_1572_);
lean_ctor_set(v___x_1581_, 10, v___x_1573_);
lean_ctor_set(v___x_1581_, 11, v___x_1574_);
lean_ctor_set(v___x_1581_, 12, v___x_1575_);
lean_ctor_set(v___x_1581_, 13, v___x_1558_);
lean_ctor_set(v___x_1581_, 14, v___x_1576_);
lean_ctor_set(v___x_1581_, 15, v___x_1578_);
lean_ctor_set(v___x_1581_, 16, v___x_1579_);
lean_ctor_set(v___x_1581_, 17, v___x_1580_);
lean_ctor_set(v___x_1581_, 18, v___x_1578_);
lean_ctor_set(v___x_1581_, 19, v___x_1579_);
lean_ctor_set(v___x_1581_, 20, v___x_1580_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*21, v___x_1577_);
v___x_1582_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1553_, v___x_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1585_, lean_object* v_collocated_1586_, lean_object* v_a_1587_){
_start:
{
uint8_t v_collocated_boxed_1588_; lean_object* v_res_1589_; 
v_collocated_boxed_1588_ = lean_unbox(v_collocated_1586_);
v_res_1589_ = l_Lake_LeanInstall_get(v_sysroot_1585_, v_collocated_boxed_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lake_findLeanSysroot_x3f(v_lean_1590_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_box(0);
return v___x_1593_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1603_; 
v_val_1594_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1596_ = v___x_1592_;
v_isShared_1597_ = v_isSharedCheck_1603_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v___x_1592_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1603_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1598_ = 0;
v___x_1599_ = l_Lake_LeanInstall_get(v_val_1594_, v___x_1598_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_io_app_path();
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_System_FilePath_parent(v_a_1611_);
if (lean_obj_tag(v___x_1612_) == 1)
{
lean_object* v_val_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_val_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc_n(v_val_1613_, 2);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1615_ = l_System_FilePath_join(v_val_1613_, v___x_1614_);
v___x_1616_ = l_System_FilePath_exeExtension;
v___x_1617_ = l_System_FilePath_addExtension(v___x_1615_, v___x_1616_);
v___x_1618_ = l_System_FilePath_pathExists(v___x_1617_);
lean_dec_ref(v___x_1617_);
if (v___x_1618_ == 0)
{
lean_dec(v_val_1613_);
goto v___jp_1608_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = l_System_FilePath_parent(v_val_1613_);
return v___x_1619_;
}
}
else
{
lean_dec(v___x_1612_);
goto v___jp_1608_;
}
}
else
{
lean_dec_ref_known(v___x_1610_, 1);
goto v___jp_1608_;
}
v___jp_1608_:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_box(0);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_System_FilePath_parent(v_lake_1622_);
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
if (lean_obj_tag(v___x_1627_) == 0)
{
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1629_; 
v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = l_System_FilePath_parent(v_val_1628_);
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1631_){
_start:
{
lean_object* v___x_1633_; 
lean_inc_ref(v_lake_1631_);
v___x_1633_ = l_Lake_lakeBuildHome_x3f(v_lake_1631_);
if (lean_obj_tag(v___x_1633_) == 1)
{
lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1658_; 
v_val_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1658_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1658_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_lake_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1638_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1634_, 2);
v___x_1639_ = l_System_FilePath_join(v_val_1634_, v___x_1638_);
v___x_1640_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1639_);
v___x_1641_ = l_System_FilePath_join(v___x_1639_, v___x_1640_);
v___x_1642_ = l_Lake_defaultLeanLibDir;
v___x_1643_ = l_System_FilePath_join(v___x_1639_, v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1645_ = 0;
v___x_1646_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref_n(v___x_1643_, 2);
v___x_1647_ = l_System_FilePath_join(v___x_1643_, v___x_1646_);
v___x_1648_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1649_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1644_);
lean_ctor_set(v___x_1649_, 2, v___x_1648_);
lean_ctor_set(v___x_1649_, 3, v___x_1648_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*4, v___x_1645_);
v_lake_1650_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1650_, 0, v_val_1634_);
lean_ctor_set(v_lake_1650_, 1, v_val_1634_);
lean_ctor_set(v_lake_1650_, 2, v___x_1641_);
lean_ctor_set(v_lake_1650_, 3, v___x_1643_);
lean_ctor_set(v_lake_1650_, 4, v___x_1649_);
lean_ctor_set(v_lake_1650_, 5, v_lake_1631_);
v___x_1651_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1652_ = l_System_FilePath_join(v___x_1643_, v___x_1651_);
v___x_1653_ = l_System_FilePath_pathExists(v___x_1652_);
lean_dec_ref(v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec_ref_known(v_lake_1650_, 6);
lean_del_object(v___x_1636_);
v___x_1654_ = lean_box(0);
return v___x_1654_;
}
else
{
lean_object* v___x_1656_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_lake_1650_);
v___x_1656_ = v___x_1636_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_lake_1650_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v___x_1659_; 
lean_dec(v___x_1633_);
lean_dec_ref(v_lake_1631_);
v___x_1659_ = lean_box(0);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lake_getLakeInstall_x3f(v_lake_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v_lean_1667_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1681_ = lean_io_getenv(v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 1)
{
lean_object* v_val_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_val_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1686_ = 0;
v___x_1687_ = l_Lake_LeanInstall_get(v_val_1682_, v___x_1686_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1687_);
v___x_1689_ = v___x_1684_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v___x_1681_);
v___x_1692_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1693_ = lean_io_getenv(v___x_1692_);
if (lean_obj_tag(v___x_1693_) == 1)
{
lean_object* v_val_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_startInclusive_1699_; lean_object* v_endExclusive_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_val_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc_n(v_val_1694_, 2);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_string_utf8_byte_size(v_val_1694_);
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v_val_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
v___x_1698_ = l_String_Slice_trimAscii(v___x_1697_);
v_startInclusive_1699_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_startInclusive_1699_);
v_endExclusive_1700_ = lean_ctor_get(v___x_1698_, 2);
lean_inc(v_endExclusive_1700_);
lean_dec_ref(v___x_1698_);
v___x_1701_ = lean_nat_sub(v_endExclusive_1700_, v_startInclusive_1699_);
lean_dec(v_startInclusive_1699_);
lean_dec(v_endExclusive_1700_);
v___x_1702_ = lean_nat_dec_eq(v___x_1701_, v___x_1695_);
lean_dec(v___x_1701_);
if (v___x_1702_ == 0)
{
v_lean_1667_ = v_val_1694_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1703_; 
lean_dec(v_val_1694_);
v___x_1703_ = lean_box(0);
return v___x_1703_;
}
}
else
{
lean_object* v___x_1704_; 
lean_dec(v___x_1693_);
v___x_1704_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v_lean_1667_ = v___x_1704_;
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lake_findLeanSysroot_x3f(v_lean_1667_);
if (lean_obj_tag(v___x_1668_) == 1)
{
lean_object* v_val_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1678_; 
v_val_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_val_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1673_ = 0;
v___x_1674_ = l_Lake_LeanInstall_get(v_val_1669_, v___x_1673_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v___x_1679_; 
lean_dec(v___x_1668_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lake_findLeanInstall_x3f();
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
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
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lake_findLakeInstall_x3f();
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = l_Lake_findElanInstall_x3f();
v___x_1744_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1744_) == 1)
{
lean_object* v_val_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1802_; 
v_val_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1802_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_val_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1802_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1750_ = lean_io_getenv(v___x_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
goto v___jp_1751_;
}
else
{
lean_object* v_val_1761_; lean_object* v___x_1762_; 
v_val_1761_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1762_ = l_Lake_envToBool_x3f(v_val_1761_);
if (lean_obj_tag(v___x_1762_) == 0)
{
goto v___jp_1751_;
}
else
{
lean_object* v_val_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1801_; 
v_val_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1801_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_val_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1801_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_unbox(v_val_1763_);
if (v___x_1767_ == 0)
{
lean_del_object(v___x_1765_);
lean_dec(v_val_1763_);
goto v___jp_1751_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_del_object(v___x_1747_);
v___x_1768_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1769_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
lean_inc_n(v_val_1745_, 10);
v___x_1770_ = l_System_FilePath_join(v_val_1745_, v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1772_ = l_System_FilePath_join(v___x_1770_, v___x_1771_);
v___x_1773_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1774_ = l_System_FilePath_join(v_val_1745_, v___x_1773_);
lean_inc_ref(v___x_1774_);
v___x_1775_ = l_System_FilePath_join(v___x_1774_, v___x_1771_);
v___x_1776_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1777_ = l_System_FilePath_join(v_val_1745_, v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1779_ = l_System_FilePath_join(v_val_1745_, v___x_1778_);
v___x_1780_ = l_Lake_leanExe(v_val_1745_);
v___x_1781_ = l_Lake_leanirExe(v_val_1745_);
v___x_1782_ = l_Lake_leancExe(v_val_1745_);
v___x_1783_ = l_Lake_leantarExe(v_val_1745_);
v___x_1784_ = l_Lake_leanSharedDynlibs(v_val_1745_);
v___x_1785_ = l_Lake_leanSharedDynlib(v_val_1745_);
v___x_1786_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_1787_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1788_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1789_ = lean_unbox(v_val_1763_);
v___x_1790_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1789_);
v___x_1791_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
lean_inc_ref(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1792_, 0, v_val_1745_);
lean_ctor_set(v___x_1792_, 1, v___x_1768_);
lean_ctor_set(v___x_1792_, 2, v___x_1772_);
lean_ctor_set(v___x_1792_, 3, v___x_1775_);
lean_ctor_set(v___x_1792_, 4, v___x_1777_);
lean_ctor_set(v___x_1792_, 5, v___x_1774_);
lean_ctor_set(v___x_1792_, 6, v___x_1779_);
lean_ctor_set(v___x_1792_, 7, v___x_1780_);
lean_ctor_set(v___x_1792_, 8, v___x_1781_);
lean_ctor_set(v___x_1792_, 9, v___x_1782_);
lean_ctor_set(v___x_1792_, 10, v___x_1783_);
lean_ctor_set(v___x_1792_, 11, v___x_1784_);
lean_ctor_set(v___x_1792_, 12, v___x_1785_);
lean_ctor_set(v___x_1792_, 13, v___x_1786_);
lean_ctor_set(v___x_1792_, 14, v___x_1787_);
lean_ctor_set(v___x_1792_, 15, v___x_1788_);
lean_ctor_set(v___x_1792_, 16, v___x_1790_);
lean_ctor_set(v___x_1792_, 17, v___x_1791_);
lean_ctor_set(v___x_1792_, 18, v___x_1788_);
lean_ctor_set(v___x_1792_, 19, v___x_1790_);
lean_ctor_set(v___x_1792_, 20, v___x_1791_);
v___x_1793_ = lean_unbox(v_val_1763_);
lean_dec(v_val_1763_);
lean_ctor_set_uint8(v___x_1792_, sizeof(void*)*21, v___x_1793_);
v___x_1794_ = l_Lake_LakeInstall_ofLean(v___x_1792_);
v___x_1795_ = l_Lake_findLeanInstall_x3f();
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1794_);
v___x_1797_ = v___x_1765_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1794_);
v___x_1797_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1795_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1743_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
return v___x_1799_;
}
}
}
}
}
v___jp_1751_:
{
uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1752_ = 1;
v___x_1753_ = l_Lake_LeanInstall_get(v_val_1745_, v___x_1752_);
lean_inc_ref(v___x_1753_);
v___x_1754_ = l_Lake_LakeInstall_ofLean(v___x_1753_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1753_);
v___x_1756_ = v___x_1747_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1753_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1754_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1743_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
return v___x_1759_;
}
}
}
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v___x_1744_);
v___x_1803_ = l_Lake_findLeanInstall_x3f();
v___x_1804_ = l_Lake_findLakeInstall_x3f();
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1743_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
return v___x_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lake_findInstall_x3f();
return v_res_1808_;
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
