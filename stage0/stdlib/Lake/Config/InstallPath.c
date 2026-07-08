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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib(lean_object* v_sysroot_322_, lean_object* v_name_323_, lean_object* v_deps_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_325_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_326_ = l_System_FilePath_join(v_sysroot_322_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_328_ = lean_string_append(v___x_327_, v_name_323_);
v___x_329_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__0));
v___x_330_ = lean_string_append(v___x_328_, v___x_329_);
v___x_331_ = l_System_FilePath_join(v___x_326_, v___x_330_);
v___x_332_ = 0;
v___x_333_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_334_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_334_, 0, v___x_331_);
lean_ctor_set(v___x_334_, 1, v_name_323_);
lean_ctor_set(v___x_334_, 2, v_deps_324_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*4, v___x_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg(lean_object* v_sysroot_336_, lean_object* v_name_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_338_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_339_ = l_System_FilePath_join(v_sysroot_336_, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_341_ = l_System_FilePath_join(v___x_339_, v___x_340_);
v___x_342_ = lean_string_append(v___x_338_, v_name_337_);
v___x_343_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_344_ = lean_string_append(v___x_342_, v___x_343_);
v___x_345_ = l_Lake_sharedLibExt;
v___x_346_ = lean_string_append(v___x_344_, v___x_345_);
v___x_347_ = l_System_FilePath_join(v___x_341_, v___x_346_);
v___x_348_ = 0;
v___x_349_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_350_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_350_, 0, v___x_347_);
lean_ctor_set(v___x_350_, 1, v_name_337_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_ctor_set(v___x_350_, 3, v___x_349_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*4, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(lean_object* v_sysroot_351_, lean_object* v_name_352_, lean_object* v_x_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_354_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_355_ = l_System_FilePath_join(v_sysroot_351_, v___x_354_);
v___x_356_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_357_ = l_System_FilePath_join(v___x_355_, v___x_356_);
v___x_358_ = lean_string_append(v___x_354_, v_name_352_);
v___x_359_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___redArg___closed__0));
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
v___x_361_ = l_Lake_sharedLibExt;
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
v___x_363_ = l_System_FilePath_join(v___x_357_, v___x_362_);
v___x_364_ = 0;
v___x_365_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_366_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v_name_352_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
lean_ctor_set(v___x_366_, 3, v___x_365_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*4, v___x_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib___boxed(lean_object* v_sysroot_367_, lean_object* v_name_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_unixLib(v_sysroot_367_, v_name_368_, v_x_369_);
lean_dec_ref(v_x_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs(lean_object* v_f_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_init_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_lean1_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_lean2_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_lean_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_376_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_377_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
lean_inc_ref_n(v_f_375_, 3);
v_init_378_ = lean_apply_2(v_f_375_, v___x_376_, v___x_377_);
v___x_379_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_380_);
lean_inc_ref_n(v_init_378_, 3);
v___x_382_ = lean_array_push(v___x_381_, v_init_378_);
v_lean1_383_ = lean_apply_2(v_f_375_, v___x_379_, v___x_382_);
v___x_384_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_385_ = lean_unsigned_to_nat(2u);
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_385_);
lean_inc_ref_n(v_lean1_383_, 2);
v___x_387_ = lean_array_push(v___x_386_, v_lean1_383_);
v___x_388_ = lean_array_push(v___x_387_, v_init_378_);
v_lean2_389_ = lean_apply_2(v_f_375_, v___x_384_, v___x_388_);
v___x_390_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_mk_empty_array_with_capacity(v___x_391_);
lean_inc_ref(v_lean2_389_);
v___x_393_ = lean_array_push(v___x_392_, v_lean2_389_);
v___x_394_ = lean_array_push(v___x_393_, v_lean1_383_);
v___x_395_ = lean_array_push(v___x_394_, v_init_378_);
v_lean_396_ = lean_apply_2(v_f_375_, v___x_390_, v___x_395_);
v___x_397_ = lean_unsigned_to_nat(4u);
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_397_);
v___x_399_ = lean_array_push(v___x_398_, v_lean_396_);
v___x_400_ = lean_array_push(v___x_399_, v_lean2_389_);
v___x_401_ = lean_array_push(v___x_400_, v_lean1_383_);
v___x_402_ = lean_array_push(v___x_401_, v_init_378_);
return v___x_402_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = l_Lake_sharedLibExt;
v___x_405_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__0));
v___x_406_ = lean_string_append(v___x_405_, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = l_Lake_sharedLibExt;
v___x_409_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__2));
v___x_410_ = lean_string_append(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__5(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = l_Lake_sharedLibExt;
v___x_413_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__4));
v___x_414_ = lean_string_append(v___x_413_, v___x_412_);
return v___x_414_;
}
}
static lean_object* _init_l_Lake_leanSharedDynlibs___closed__7(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = l_Lake_sharedLibExt;
v___x_417_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__6));
v___x_418_ = lean_string_append(v___x_417_, v___x_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlibs(lean_object* v_sysroot_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_System_Platform_isWindows;
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_init_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_lean1_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_lean2_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_lean_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_425_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_426_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_427_ = l_System_FilePath_join(v_sysroot_423_, v___x_426_);
v___x_428_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_429_ = l_System_FilePath_join(v___x_427_, v___x_428_);
v___x_430_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__1, &l_Lake_leanSharedDynlibs___closed__1_once, _init_l_Lake_leanSharedDynlibs___closed__1);
lean_inc_ref_n(v___x_429_, 3);
v___x_431_ = l_System_FilePath_join(v___x_429_, v___x_430_);
v___x_432_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v_init_433_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_433_, 0, v___x_431_);
lean_ctor_set(v_init_433_, 1, v___x_425_);
lean_ctor_set(v_init_433_, 2, v___x_432_);
lean_ctor_set(v_init_433_, 3, v___x_432_);
lean_ctor_set_uint8(v_init_433_, sizeof(void*)*4, v___x_424_);
v___x_434_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_435_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__3, &l_Lake_leanSharedDynlibs___closed__3_once, _init_l_Lake_leanSharedDynlibs___closed__3);
v___x_436_ = l_System_FilePath_join(v___x_429_, v___x_435_);
v_lean1_437_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_437_, 0, v___x_436_);
lean_ctor_set(v_lean1_437_, 1, v___x_434_);
lean_ctor_set(v_lean1_437_, 2, v___x_432_);
lean_ctor_set(v_lean1_437_, 3, v___x_432_);
lean_ctor_set_uint8(v_lean1_437_, sizeof(void*)*4, v___x_424_);
v___x_438_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_439_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__5, &l_Lake_leanSharedDynlibs___closed__5_once, _init_l_Lake_leanSharedDynlibs___closed__5);
v___x_440_ = l_System_FilePath_join(v___x_429_, v___x_439_);
v_lean2_441_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_441_, 0, v___x_440_);
lean_ctor_set(v_lean2_441_, 1, v___x_438_);
lean_ctor_set(v_lean2_441_, 2, v___x_432_);
lean_ctor_set(v_lean2_441_, 3, v___x_432_);
lean_ctor_set_uint8(v_lean2_441_, sizeof(void*)*4, v___x_424_);
v___x_442_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_443_ = lean_obj_once(&l_Lake_leanSharedDynlibs___closed__7, &l_Lake_leanSharedDynlibs___closed__7_once, _init_l_Lake_leanSharedDynlibs___closed__7);
v___x_444_ = l_System_FilePath_join(v___x_429_, v___x_443_);
v_lean_445_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_445_, 0, v___x_444_);
lean_ctor_set(v_lean_445_, 1, v___x_442_);
lean_ctor_set(v_lean_445_, 2, v___x_432_);
lean_ctor_set(v_lean_445_, 3, v___x_432_);
lean_ctor_set_uint8(v_lean_445_, sizeof(void*)*4, v___x_424_);
v___x_446_ = lean_unsigned_to_nat(4u);
v___x_447_ = lean_mk_empty_array_with_capacity(v___x_446_);
v___x_448_ = lean_array_push(v___x_447_, v_lean_445_);
v___x_449_ = lean_array_push(v___x_448_, v_lean2_441_);
v___x_450_ = lean_array_push(v___x_449_, v_lean1_437_);
v___x_451_ = lean_array_push(v___x_450_, v_init_433_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v_init_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_lean1_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_lean2_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_lean_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_452_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__0));
v___x_453_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_454_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_455_ = l_System_FilePath_join(v_sysroot_423_, v___x_454_);
v___x_456_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__8));
lean_inc_ref_n(v___x_455_, 3);
v___x_457_ = l_System_FilePath_join(v___x_455_, v___x_456_);
v___x_458_ = 0;
v_init_459_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_init_459_, 0, v___x_457_);
lean_ctor_set(v_init_459_, 1, v___x_452_);
lean_ctor_set(v_init_459_, 2, v___x_453_);
lean_ctor_set(v_init_459_, 3, v___x_453_);
lean_ctor_set_uint8(v_init_459_, sizeof(void*)*4, v___x_458_);
v___x_460_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__1));
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_mk_empty_array_with_capacity(v___x_461_);
lean_inc_ref_n(v_init_459_, 3);
v___x_463_ = lean_array_push(v___x_462_, v_init_459_);
v___x_464_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__9));
v___x_465_ = l_System_FilePath_join(v___x_455_, v___x_464_);
v_lean1_466_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean1_466_, 0, v___x_465_);
lean_ctor_set(v_lean1_466_, 1, v___x_460_);
lean_ctor_set(v_lean1_466_, 2, v___x_463_);
lean_ctor_set(v_lean1_466_, 3, v___x_453_);
lean_ctor_set_uint8(v_lean1_466_, sizeof(void*)*4, v___x_458_);
v___x_467_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__2));
v___x_468_ = lean_unsigned_to_nat(2u);
v___x_469_ = lean_mk_empty_array_with_capacity(v___x_468_);
lean_inc_ref_n(v_lean1_466_, 2);
v___x_470_ = lean_array_push(v___x_469_, v_lean1_466_);
v___x_471_ = lean_array_push(v___x_470_, v_init_459_);
v___x_472_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__10));
v___x_473_ = l_System_FilePath_join(v___x_455_, v___x_472_);
v_lean2_474_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean2_474_, 0, v___x_473_);
lean_ctor_set(v_lean2_474_, 1, v___x_467_);
lean_ctor_set(v_lean2_474_, 2, v___x_471_);
lean_ctor_set(v_lean2_474_, 3, v___x_453_);
lean_ctor_set_uint8(v_lean2_474_, sizeof(void*)*4, v___x_458_);
v___x_475_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_libs___closed__3));
v___x_476_ = lean_unsigned_to_nat(3u);
v___x_477_ = lean_mk_empty_array_with_capacity(v___x_476_);
lean_inc_ref(v_lean2_474_);
v___x_478_ = lean_array_push(v___x_477_, v_lean2_474_);
v___x_479_ = lean_array_push(v___x_478_, v_lean1_466_);
v___x_480_ = lean_array_push(v___x_479_, v_init_459_);
v___x_481_ = ((lean_object*)(l_Lake_leanSharedDynlibs___closed__11));
v___x_482_ = l_System_FilePath_join(v___x_455_, v___x_481_);
v_lean_483_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_lean_483_, 0, v___x_482_);
lean_ctor_set(v_lean_483_, 1, v___x_475_);
lean_ctor_set(v_lean_483_, 2, v___x_480_);
lean_ctor_set(v_lean_483_, 3, v___x_453_);
lean_ctor_set_uint8(v_lean_483_, sizeof(void*)*4, v___x_458_);
v___x_484_ = lean_unsigned_to_nat(4u);
v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
v___x_486_ = lean_array_push(v___x_485_, v_lean_483_);
v___x_487_ = lean_array_push(v___x_486_, v_lean2_474_);
v___x_488_ = lean_array_push(v___x_487_, v_lean1_466_);
v___x_489_ = lean_array_push(v___x_488_, v_init_459_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedDynlib(lean_object* v_sysroot_490_){
_start:
{
lean_object* v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = l_Lake_leanSharedDynlibs(v_sysroot_490_);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = lean_array_uget(v___x_491_, v___x_492_);
lean_dec_ref(v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l_Lake_leanSharedLib___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = l_Lake_sharedLibExt;
v___x_496_ = ((lean_object*)(l_Lake_leanSharedLib___closed__0));
v___x_497_ = l_System_FilePath_addExtension(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lake_leanSharedLib(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_Lake_leanSharedLib___closed__1, &l_Lake_leanSharedLib___closed__1_once, _init_l_Lake_leanSharedLib___closed__1);
return v___x_498_;
}
}
static lean_object* _init_l_Lake_initSharedLib___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = l_Lake_sharedLibExt;
v___x_501_ = ((lean_object*)(l_Lake_initSharedLib___closed__0));
v___x_502_ = l_System_FilePath_addExtension(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lake_initSharedLib(void){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lake_initSharedLib___closed__1, &l_Lake_initSharedLib___closed__1_once, _init_l_Lake_initSharedLib___closed__1);
return v___x_503_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_506_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_507_ = l_System_FilePath_join(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__2(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_509_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__1, &l_Lake_instInhabitedLeanInstall_default___closed__1_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__1);
v___x_510_ = l_System_FilePath_join(v___x_509_, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_512_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_513_ = l_System_FilePath_join(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__4(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_515_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_516_ = l_System_FilePath_join(v___x_515_, v___x_514_);
return v___x_516_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__6(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_519_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_520_ = l_System_FilePath_join(v___x_519_, v___x_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__7(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_522_ = l_Lake_leanExe(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__8(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_524_ = l_Lake_leanirExe(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__9(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_526_ = l_Lake_leancExe(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__10(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_528_ = l_Lake_leantarExe(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__11(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_530_ = l_Lake_leanSharedDynlibs(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__12(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_532_ = l_Lake_leanSharedDynlib(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__16(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__15));
v___x_537_ = l_Lean_Compiler_FFI_getCFlags_x27;
v___x_538_ = lean_array_push(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__17(void){
_start:
{
uint8_t v___x_539_; lean_object* v___x_540_; 
v___x_539_ = 1;
v___x_540_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__18(void){
_start:
{
uint8_t v___x_541_; lean_object* v___x_542_; 
v___x_541_ = 0;
v___x_542_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default___closed__19(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_543_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_544_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_545_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_546_ = 1;
v___x_547_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_548_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_549_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__12, &l_Lake_instInhabitedLeanInstall_default___closed__12_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__12);
v___x_550_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__11, &l_Lake_instInhabitedLeanInstall_default___closed__11_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__11);
v___x_551_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__10, &l_Lake_instInhabitedLeanInstall_default___closed__10_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__10);
v___x_552_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__9, &l_Lake_instInhabitedLeanInstall_default___closed__9_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__9);
v___x_553_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__8, &l_Lake_instInhabitedLeanInstall_default___closed__8_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__8);
v___x_554_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__7, &l_Lake_instInhabitedLeanInstall_default___closed__7_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__7);
v___x_555_ = lean_obj_once(&l_Lake_instInhabitedElanInstall_default___closed__2, &l_Lake_instInhabitedElanInstall_default___closed__2_once, _init_l_Lake_instInhabitedElanInstall_default___closed__2);
v___x_556_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__3, &l_Lake_instInhabitedLeanInstall_default___closed__3_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__3);
v___x_557_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__6, &l_Lake_instInhabitedLeanInstall_default___closed__6_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__6);
v___x_558_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__4, &l_Lake_instInhabitedLeanInstall_default___closed__4_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__4);
v___x_559_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__2, &l_Lake_instInhabitedLeanInstall_default___closed__2_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__2);
v___x_560_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_561_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
lean_ctor_set(v___x_561_, 2, v___x_559_);
lean_ctor_set(v___x_561_, 3, v___x_558_);
lean_ctor_set(v___x_561_, 4, v___x_557_);
lean_ctor_set(v___x_561_, 5, v___x_556_);
lean_ctor_set(v___x_561_, 6, v___x_555_);
lean_ctor_set(v___x_561_, 7, v___x_554_);
lean_ctor_set(v___x_561_, 8, v___x_553_);
lean_ctor_set(v___x_561_, 9, v___x_552_);
lean_ctor_set(v___x_561_, 10, v___x_551_);
lean_ctor_set(v___x_561_, 11, v___x_550_);
lean_ctor_set(v___x_561_, 12, v___x_549_);
lean_ctor_set(v___x_561_, 13, v___x_548_);
lean_ctor_set(v___x_561_, 14, v___x_547_);
lean_ctor_set(v___x_561_, 15, v___x_545_);
lean_ctor_set(v___x_561_, 16, v___x_544_);
lean_ctor_set(v___x_561_, 17, v___x_543_);
lean_ctor_set(v___x_561_, 18, v___x_545_);
lean_ctor_set(v___x_561_, 19, v___x_544_);
lean_ctor_set(v___x_561_, 20, v___x_543_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*21, v___x_546_);
return v___x_561_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall_default(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__19, &l_Lake_instInhabitedLeanInstall_default___closed__19_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__19);
return v___x_562_;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lake_instInhabitedLeanInstall_default;
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_dec(v_x_564_);
return v_x_565_;
}
else
{
lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_579_; 
v_head_567_ = lean_ctor_get(v_x_566_, 0);
v_tail_568_ = lean_ctor_get(v_x_566_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_566_);
if (v_isSharedCheck_579_ == 0)
{
v___x_570_ = v_x_566_;
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_tail_568_);
lean_inc(v_head_567_);
lean_dec(v_x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
lean_inc(v_x_564_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 5);
lean_ctor_set(v___x_570_, 1, v_x_564_);
lean_ctor_set(v___x_570_, 0, v_x_565_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_x_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_x_564_);
v___x_573_ = v_reuseFailAlloc_578_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l_String_quote(v_head_567_);
v___x_575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v_x_565_ = v___x_576_;
v_x_566_ = v_tail_568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_dec(v_x_580_);
return v_x_581_;
}
else
{
lean_object* v_head_583_; lean_object* v_tail_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_595_; 
v_head_583_ = lean_ctor_get(v_x_582_, 0);
v_tail_584_ = lean_ctor_get(v_x_582_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_595_ == 0)
{
v___x_586_ = v_x_582_;
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_tail_584_);
lean_inc(v_head_583_);
lean_dec(v_x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
lean_inc(v_x_580_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 5);
lean_ctor_set(v___x_586_, 1, v_x_580_);
lean_ctor_set(v___x_586_, 0, v_x_581_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_x_581_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_x_580_);
v___x_589_ = v_reuseFailAlloc_594_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = l_String_quote(v_head_583_);
v___x_591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
v___x_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_589_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4_spec__6(v_x_580_, v___x_592_, v_tail_584_);
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(lean_object* v___y_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = l_String_quote(v___y_596_);
v___x_598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
lean_object* v___x_601_; 
lean_dec(v_x_600_);
v___x_601_ = lean_box(0);
return v___x_601_;
}
else
{
lean_object* v_tail_602_; 
v_tail_602_ = lean_ctor_get(v_x_599_, 1);
if (lean_obj_tag(v_tail_602_) == 0)
{
lean_object* v_head_603_; lean_object* v___x_604_; 
lean_dec(v_x_600_);
v_head_603_ = lean_ctor_get(v_x_599_, 0);
lean_inc(v_head_603_);
lean_dec_ref_known(v_x_599_, 2);
v___x_604_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_603_);
return v___x_604_;
}
else
{
lean_object* v_head_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_inc(v_tail_602_);
v_head_605_ = lean_ctor_get(v_x_599_, 0);
lean_inc(v_head_605_);
lean_dec_ref_known(v_x_599_, 2);
v___x_606_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2___lam__0(v_head_605_);
v___x_607_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2_spec__4(v_x_600_, v___x_606_, v_tail_602_);
return v___x_607_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__0));
v___x_614_ = lean_string_length(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__3);
v___x_616_ = lean_nat_to_int(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(lean_object* v_xs_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_array_get_size(v_xs_624_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_nat_dec_eq(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_628_ = lean_array_to_list(v_xs_624_);
v___x_629_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_630_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1_spec__2(v___x_628_, v___x_629_);
v___x_631_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_632_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_630_);
v___x_634_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_631_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Std_Format_fill(v___x_636_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
lean_dec_ref(v_xs_624_);
v___x_638_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_dec(v_x_639_);
return v_x_640_;
}
else
{
lean_object* v_head_642_; lean_object* v_tail_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_653_; 
v_head_642_ = lean_ctor_get(v_x_641_, 0);
v_tail_643_ = lean_ctor_get(v_x_641_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_653_ == 0)
{
v___x_645_ = v_x_641_;
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_tail_643_);
lean_inc(v_head_642_);
lean_dec(v_x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
lean_inc(v_x_639_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 5);
lean_ctor_set(v___x_645_, 1, v_x_639_);
lean_ctor_set(v___x_645_, 0, v_x_640_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_x_640_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_x_639_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = l_Lake_instReprDynlib_repr___redArg(v_head_642_);
v___x_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v_x_640_ = v___x_650_;
v_x_641_ = v_tail_643_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_dec(v_x_654_);
return v_x_655_;
}
else
{
lean_object* v_head_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v_head_657_ = lean_ctor_get(v_x_656_, 0);
v_tail_658_ = lean_ctor_get(v_x_656_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_668_ == 0)
{
v___x_660_ = v_x_656_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_head_657_);
lean_dec(v_x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
lean_inc(v_x_654_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 5);
lean_ctor_set(v___x_660_, 1, v_x_654_);
lean_ctor_set(v___x_660_, 0, v_x_655_);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_x_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_x_654_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = l_Lake_instReprDynlib_repr___redArg(v_head_657_);
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__3(v_x_654_, v___x_665_, v_tail_658_);
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v___x_671_; 
lean_dec(v_x_670_);
v___x_671_ = lean_box(0);
return v___x_671_;
}
else
{
lean_object* v_tail_672_; 
v_tail_672_ = lean_ctor_get(v_x_669_, 1);
if (lean_obj_tag(v_tail_672_) == 0)
{
lean_object* v_head_673_; lean_object* v___x_674_; 
lean_dec(v_x_670_);
v_head_673_ = lean_ctor_get(v_x_669_, 0);
lean_inc(v_head_673_);
lean_dec_ref_known(v_x_669_, 2);
v___x_674_ = l_Lake_instReprDynlib_repr___redArg(v_head_673_);
return v___x_674_;
}
else
{
lean_object* v_head_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_inc(v_tail_672_);
v_head_675_ = lean_ctor_get(v_x_669_, 0);
lean_inc(v_head_675_);
lean_dec_ref_known(v_x_669_, 2);
v___x_676_ = l_Lake_instReprDynlib_repr___redArg(v_head_675_);
v___x_677_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_670_, v___x_676_, v_tail_672_);
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(lean_object* v_xs_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = lean_array_get_size(v_xs_678_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_nat_dec_eq(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_682_ = lean_array_to_list(v_xs_678_);
v___x_683_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__1));
v___x_684_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_682_, v___x_683_);
v___x_685_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4, &l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4_once, _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__4);
v___x_686_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__5));
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_684_);
v___x_688_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__6));
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_685_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Std_Format_fill(v___x_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; 
lean_dec_ref(v_xs_678_);
v___x_692_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1___closed__8));
return v___x_692_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(11u);
v___x_703_ = lean_nat_to_int(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(14u);
v___x_714_ = lean_nat_to_int(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(16u);
v___x_722_ = lean_nat_to_int(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(9u);
v___x_730_ = lean_nat_to_int(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(6u);
v___x_742_ = lean_nat_to_int(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(12u);
v___x_749_ = lean_nat_to_int(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(19u);
v___x_757_ = lean_nat_to_int(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(21u);
v___x_768_ = lean_nat_to_int(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___redArg(lean_object* v_x_772_){
_start:
{
lean_object* v_sysroot_773_; lean_object* v_githash_774_; lean_object* v_srcDir_775_; lean_object* v_leanLibDir_776_; lean_object* v_includeDir_777_; lean_object* v_systemLibDir_778_; lean_object* v_binDir_779_; lean_object* v_lean_780_; lean_object* v_leanir_781_; lean_object* v_leanc_782_; lean_object* v_leantar_783_; lean_object* v_sharedDynlibs_784_; lean_object* v_sharedDynlib_785_; lean_object* v_ar_786_; lean_object* v_cc_787_; uint8_t v_customCc_788_; lean_object* v_cFlags_789_; lean_object* v_linkStaticFlags_790_; lean_object* v_linkSharedFlags_791_; lean_object* v_ccFlags_792_; lean_object* v_ccLinkStaticFlags_793_; lean_object* v_ccLinkSharedFlags_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_sysroot_773_ = lean_ctor_get(v_x_772_, 0);
lean_inc_ref(v_sysroot_773_);
v_githash_774_ = lean_ctor_get(v_x_772_, 1);
lean_inc_ref(v_githash_774_);
v_srcDir_775_ = lean_ctor_get(v_x_772_, 2);
lean_inc_ref(v_srcDir_775_);
v_leanLibDir_776_ = lean_ctor_get(v_x_772_, 3);
lean_inc_ref(v_leanLibDir_776_);
v_includeDir_777_ = lean_ctor_get(v_x_772_, 4);
lean_inc_ref(v_includeDir_777_);
v_systemLibDir_778_ = lean_ctor_get(v_x_772_, 5);
lean_inc_ref(v_systemLibDir_778_);
v_binDir_779_ = lean_ctor_get(v_x_772_, 6);
lean_inc_ref(v_binDir_779_);
v_lean_780_ = lean_ctor_get(v_x_772_, 7);
lean_inc_ref(v_lean_780_);
v_leanir_781_ = lean_ctor_get(v_x_772_, 8);
lean_inc_ref(v_leanir_781_);
v_leanc_782_ = lean_ctor_get(v_x_772_, 9);
lean_inc_ref(v_leanc_782_);
v_leantar_783_ = lean_ctor_get(v_x_772_, 10);
lean_inc_ref(v_leantar_783_);
v_sharedDynlibs_784_ = lean_ctor_get(v_x_772_, 11);
lean_inc_ref(v_sharedDynlibs_784_);
v_sharedDynlib_785_ = lean_ctor_get(v_x_772_, 12);
lean_inc_ref(v_sharedDynlib_785_);
v_ar_786_ = lean_ctor_get(v_x_772_, 13);
lean_inc_ref(v_ar_786_);
v_cc_787_ = lean_ctor_get(v_x_772_, 14);
lean_inc_ref(v_cc_787_);
v_customCc_788_ = lean_ctor_get_uint8(v_x_772_, sizeof(void*)*21);
v_cFlags_789_ = lean_ctor_get(v_x_772_, 15);
lean_inc_ref(v_cFlags_789_);
v_linkStaticFlags_790_ = lean_ctor_get(v_x_772_, 16);
lean_inc_ref(v_linkStaticFlags_790_);
v_linkSharedFlags_791_ = lean_ctor_get(v_x_772_, 17);
lean_inc_ref(v_linkSharedFlags_791_);
v_ccFlags_792_ = lean_ctor_get(v_x_772_, 18);
lean_inc_ref(v_ccFlags_792_);
v_ccLinkStaticFlags_793_ = lean_ctor_get(v_x_772_, 19);
lean_inc_ref(v_ccLinkStaticFlags_793_);
v_ccLinkSharedFlags_794_ = lean_ctor_get(v_x_772_, 20);
lean_inc_ref(v_ccLinkSharedFlags_794_);
lean_dec_ref(v_x_772_);
v___x_795_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_796_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__3));
v___x_797_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__4, &l_Lake_instReprLeanInstall_repr___redArg___closed__4_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_800_ = l_String_quote(v_sysroot_773_);
v___x_801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Repr_addAppParen(v___x_802_, v___x_798_);
v___x_804_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_797_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = 0;
v___x_806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*1, v___x_805_);
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_796_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_box(1);
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__6));
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_795_);
v___x_815_ = l_String_quote(v_githash_774_);
v___x_816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_797_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_805_);
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_814_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_808_);
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_810_);
v___x_822_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_795_);
v___x_825_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_826_ = l_String_quote(v_srcDir_775_);
v___x_827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_799_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Repr_addAppParen(v___x_828_, v___x_798_);
v___x_830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_825_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*1, v___x_805_);
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_824_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_808_);
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_810_);
v___x_835_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__10));
v___x_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_795_);
v___x_838_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__11, &l_Lake_instReprLeanInstall_repr___redArg___closed__11_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11);
v___x_839_ = l_String_quote(v_leanLibDir_776_);
v___x_840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___x_841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_799_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Repr_addAppParen(v___x_841_, v___x_798_);
v___x_843_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_838_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v___x_805_);
v___x_845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_837_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_808_);
v___x_847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_810_);
v___x_848_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__13));
v___x_849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_795_);
v___x_851_ = l_String_quote(v_includeDir_777_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_799_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Repr_addAppParen(v___x_853_, v___x_798_);
v___x_855_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_838_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_805_);
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_850_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_808_);
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_810_);
v___x_860_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__15));
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_795_);
v___x_863_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_864_ = l_String_quote(v_systemLibDir_778_);
v___x_865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_799_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Repr_addAppParen(v___x_866_, v___x_798_);
v___x_868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_863_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v___x_805_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_862_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_808_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_810_);
v___x_873_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_795_);
v___x_876_ = l_String_quote(v_binDir_779_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
v___x_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_799_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Repr_addAppParen(v___x_878_, v___x_798_);
v___x_880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_825_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_805_);
v___x_882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_875_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_808_);
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_810_);
v___x_885_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__17));
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_795_);
v___x_888_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_889_ = l_String_quote(v_lean_780_);
v___x_890_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_799_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Repr_addAppParen(v___x_891_, v___x_798_);
v___x_893_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_888_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*1, v___x_805_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_887_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_808_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_810_);
v___x_898_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__18));
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_795_);
v___x_901_ = l_String_quote(v_leanir_781_);
v___x_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_799_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Repr_addAppParen(v___x_903_, v___x_798_);
v___x_905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_825_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*1, v___x_805_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_900_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_808_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_810_);
v___x_910_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__19));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_795_);
v___x_913_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__20, &l_Lake_instReprLeanInstall_repr___redArg___closed__20_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20);
v___x_914_ = l_String_quote(v_leanc_782_);
v___x_915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_799_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Repr_addAppParen(v___x_916_, v___x_798_);
v___x_918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_913_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*1, v___x_805_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_912_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_808_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_810_);
v___x_923_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__21));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_795_);
v___x_926_ = l_String_quote(v_leantar_783_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_799_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Repr_addAppParen(v___x_928_, v___x_798_);
v___x_930_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_797_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_805_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_925_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_808_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_810_);
v___x_935_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__23));
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_795_);
v___x_938_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__19, &l_Lake_instReprElanInstall_repr___redArg___closed__19_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__19);
v___x_939_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_sharedDynlibs_784_);
v___x_940_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*1, v___x_805_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_937_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_808_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_810_);
v___x_945_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_795_);
v___x_948_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_785_);
v___x_949_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_863_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*1, v___x_805_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_947_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_808_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v___x_810_);
v___x_954_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__26));
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_795_);
v___x_957_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__27, &l_Lake_instReprLeanInstall_repr___redArg___closed__27_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__27);
v___x_958_ = l_String_quote(v_ar_786_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_799_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Repr_addAppParen(v___x_960_, v___x_798_);
v___x_962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_957_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*1, v___x_805_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_956_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_808_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_810_);
v___x_967_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__28));
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_795_);
v___x_970_ = l_String_quote(v_cc_787_);
v___x_971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_799_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Repr_addAppParen(v___x_972_, v___x_798_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_957_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_805_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_969_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_808_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_810_);
v___x_979_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__30));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_795_);
v___x_982_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__31, &l_Lake_instReprLeanInstall_repr___redArg___closed__31_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__31);
v___x_983_ = l_Bool_repr___redArg(v_customCc_788_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_805_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_981_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_808_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_810_);
v___x_989_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__33));
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_795_);
v___x_992_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_cFlags_789_);
v___x_993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_825_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*1, v___x_805_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_991_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_808_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_810_);
v___x_998_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__35));
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_795_);
v___x_1001_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__36, &l_Lake_instReprLeanInstall_repr___redArg___closed__36_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__36);
v___x_1002_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkStaticFlags_790_);
v___x_1003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1004_, sizeof(void*)*1, v___x_805_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1000_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_808_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_810_);
v___x_1008_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__38));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_795_);
v___x_1011_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_linkSharedFlags_791_);
v___x_1012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1001_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_805_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1010_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_808_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_810_);
v___x_1017_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__40));
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_795_);
v___x_1020_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccFlags_792_);
v___x_1021_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_797_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*1, v___x_805_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1019_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_808_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_810_);
v___x_1026_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__42));
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_795_);
v___x_1029_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__43, &l_Lake_instReprLeanInstall_repr___redArg___closed__43_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__43);
v___x_1030_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkStaticFlags_793_);
v___x_1031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_805_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1028_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_808_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_810_);
v___x_1036_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__45));
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_795_);
v___x_1039_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__1(v_ccLinkSharedFlags_794_);
v___x_1040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1029_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*1, v___x_805_);
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1038_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1044_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1042_);
v___x_1046_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1043_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*1, v___x_805_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr(lean_object* v_x_1050_, lean_object* v_prec_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall_repr___boxed(lean_object* v_x_1053_, lean_object* v_prec_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lake_instReprLeanInstall_repr(v_x_1053_, v_prec_1054_);
lean_dec(v_prec_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib(lean_object* v_self_1058_){
_start:
{
lean_object* v_sharedDynlib_1059_; lean_object* v_path_1060_; 
v_sharedDynlib_1059_ = lean_ctor_get(v_self_1058_, 12);
v_path_1060_ = lean_ctor_get(v_sharedDynlib_1059_, 0);
lean_inc_ref(v_path_1060_);
return v_path_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLib___boxed(lean_object* v_self_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lake_LeanInstall_sharedLib(v_self_1061_);
lean_dec_ref(v_self_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_initSharedLib(lean_object* v_self_1063_){
_start:
{
lean_object* v_sysroot_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_sysroot_1064_ = lean_ctor_get(v_self_1063_, 0);
lean_inc_ref(v_sysroot_1064_);
lean_dec_ref(v_self_1063_);
v___x_1065_ = l_Lake_leanSharedLibDir(v_sysroot_1064_);
v___x_1066_ = l_Lake_initSharedLib;
v___x_1067_ = l_System_FilePath_join(v___x_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* v_self_1068_){
_start:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_System_Platform_isWindows;
if (v___x_1069_ == 0)
{
lean_object* v_leanLibDir_1070_; lean_object* v_systemLibDir_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_leanLibDir_1070_ = lean_ctor_get(v_self_1068_, 3);
v_systemLibDir_1071_ = lean_ctor_get(v_self_1068_, 5);
v___x_1072_ = lean_box(0);
lean_inc_ref(v_systemLibDir_1071_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_systemLibDir_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
lean_inc_ref(v_leanLibDir_1070_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_leanLibDir_1070_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
return v___x_1074_;
}
else
{
lean_object* v_binDir_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_binDir_1075_ = lean_ctor_get(v_self_1068_, 6);
v___x_1076_ = lean_box(0);
lean_inc_ref(v_binDir_1075_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_binDir_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* v_self_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lake_LeanInstall_sharedLibPath(v_self_1078_);
lean_dec_ref(v_self_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* v_self_1080_){
_start:
{
uint8_t v_customCc_1081_; 
v_customCc_1081_ = lean_ctor_get_uint8(v_self_1080_, sizeof(void*)*21);
if (v_customCc_1081_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_box(0);
return v___x_1082_;
}
else
{
lean_object* v_cc_1083_; lean_object* v___x_1084_; 
v_cc_1083_ = lean_ctor_get(v_self_1080_, 14);
lean_inc_ref(v_cc_1083_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_cc_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* v_self_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lake_LeanInstall_leanCc_x3f(v_self_1085_);
lean_dec_ref(v_self_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t v_shared_1087_, lean_object* v_self_1088_){
_start:
{
if (v_shared_1087_ == 0)
{
lean_object* v_ccLinkStaticFlags_1089_; 
v_ccLinkStaticFlags_1089_ = lean_ctor_get(v_self_1088_, 19);
lean_inc_ref(v_ccLinkStaticFlags_1089_);
return v_ccLinkStaticFlags_1089_;
}
else
{
lean_object* v_ccLinkSharedFlags_1090_; 
v_ccLinkSharedFlags_1090_ = lean_ctor_get(v_self_1088_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1090_);
return v_ccLinkSharedFlags_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* v_shared_1091_, lean_object* v_self_1092_){
_start:
{
uint8_t v_shared_boxed_1093_; lean_object* v_res_1094_; 
v_shared_boxed_1093_ = lean_unbox(v_shared_1091_);
v_res_1094_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_1093_, v_self_1092_);
lean_dec_ref(v_self_1092_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lake_lakeExe___closed__1(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = l_System_FilePath_exeExtension;
v___x_1097_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1098_ = l_System_FilePath_addExtension(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lake_lakeExe(void){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_obj_once(&l_Lake_lakeExe___closed__1, &l_Lake_lakeExe___closed__1_once, _init_l_Lake_lakeExe___closed__1);
return v___x_1099_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__0(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = l_Lake_defaultBuildDir;
v___x_1101_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1102_ = l_System_FilePath_join(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = l_Lake_defaultBinDir;
v___x_1104_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1105_ = l_System_FilePath_join(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__2(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lake_defaultLeanLibDir;
v___x_1107_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__0, &l_Lake_instInhabitedLakeInstall_default___closed__0_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__0);
v___x_1108_ = l_System_FilePath_join(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__4(void){
_start:
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = 0;
v___x_1111_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1112_ = l_Lake_nameToSharedLib(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
v___x_1114_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1115_ = l_System_FilePath_join(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__6(void){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1116_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1117_ = 0;
v___x_1118_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1119_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__5, &l_Lake_instInhabitedLakeInstall_default___closed__5_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__5);
v___x_1120_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
lean_ctor_set(v___x_1120_, 2, v___x_1116_);
lean_ctor_set(v___x_1120_, 3, v___x_1116_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*4, v___x_1117_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__7(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = l_Lake_lakeExe;
v___x_1122_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1123_ = l_System_FilePath_join(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default___closed__8(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1124_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__7, &l_Lake_instInhabitedLakeInstall_default___closed__7_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__7);
v___x_1125_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__6, &l_Lake_instInhabitedLakeInstall_default___closed__6_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__6);
v___x_1126_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__2, &l_Lake_instInhabitedLakeInstall_default___closed__2_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__2);
v___x_1127_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__1, &l_Lake_instInhabitedLakeInstall_default___closed__1_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__1);
v___x_1128_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1129_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
lean_ctor_set(v___x_1129_, 2, v___x_1127_);
lean_ctor_set(v___x_1129_, 3, v___x_1126_);
lean_ctor_set(v___x_1129_, 4, v___x_1125_);
lean_ctor_set(v___x_1129_, 5, v___x_1124_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall_default(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__8, &l_Lake_instInhabitedLakeInstall_default___closed__8_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__8);
return v___x_1130_;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall(void){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lake_instInhabitedLakeInstall_default;
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___redArg(lean_object* v_x_1137_){
_start:
{
lean_object* v_home_1138_; lean_object* v_srcDir_1139_; lean_object* v_binDir_1140_; lean_object* v_libDir_1141_; lean_object* v_sharedDynlib_1142_; lean_object* v_lake_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_home_1138_ = lean_ctor_get(v_x_1137_, 0);
lean_inc_ref(v_home_1138_);
v_srcDir_1139_ = lean_ctor_get(v_x_1137_, 1);
lean_inc_ref(v_srcDir_1139_);
v_binDir_1140_ = lean_ctor_get(v_x_1137_, 2);
lean_inc_ref(v_binDir_1140_);
v_libDir_1141_ = lean_ctor_get(v_x_1137_, 3);
lean_inc_ref(v_libDir_1141_);
v_sharedDynlib_1142_ = lean_ctor_get(v_x_1137_, 4);
lean_inc_ref(v_sharedDynlib_1142_);
v_lake_1143_ = lean_ctor_get(v_x_1137_, 5);
lean_inc_ref(v_lake_1143_);
lean_dec_ref(v_x_1137_);
v___x_1144_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__5));
v___x_1145_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__6));
v___x_1146_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__7, &l_Lake_instReprElanInstall_repr___redArg___closed__7_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__7);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__9));
v___x_1149_ = l_String_quote(v_home_1138_);
v___x_1150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1148_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Repr_addAppParen(v___x_1151_, v___x_1147_);
v___x_1153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1146_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = 0;
v___x_1155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1145_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__11));
v___x_1158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_box(1);
v___x_1160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__8));
v___x_1162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1144_);
v___x_1164_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__16, &l_Lake_instReprElanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__16);
v___x_1165_ = l_String_quote(v_srcDir_1139_);
v___x_1166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1148_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Repr_addAppParen(v___x_1167_, v___x_1147_);
v___x_1169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1164_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*1, v___x_1154_);
v___x_1171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1163_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1157_);
v___x_1173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___x_1159_);
v___x_1174_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__15));
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1144_);
v___x_1177_ = l_String_quote(v_binDir_1140_);
v___x_1178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1148_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Repr_addAppParen(v___x_1179_, v___x_1147_);
v___x_1181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1164_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*1, v___x_1154_);
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1176_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1157_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1159_);
v___x_1186_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__1));
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___x_1144_);
v___x_1189_ = l_String_quote(v_libDir_1141_);
v___x_1190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1148_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Repr_addAppParen(v___x_1191_, v___x_1147_);
v___x_1193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1164_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*1, v___x_1154_);
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1188_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1157_);
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1159_);
v___x_1198_ = ((lean_object*)(l_Lake_instReprLeanInstall_repr___redArg___closed__25));
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1144_);
v___x_1201_ = lean_obj_once(&l_Lake_instReprLeanInstall_repr___redArg___closed__16, &l_Lake_instReprLeanInstall_repr___redArg___closed__16_once, _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16);
v___x_1202_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_1142_);
v___x_1203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*1, v___x_1154_);
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1200_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1157_);
v___x_1207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v___x_1159_);
v___x_1208_ = ((lean_object*)(l_Lake_instReprLakeInstall_repr___redArg___closed__2));
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1144_);
v___x_1211_ = l_String_quote(v_lake_1143_);
v___x_1212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1148_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Repr_addAppParen(v___x_1213_, v___x_1147_);
v___x_1215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1146_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*1, v___x_1154_);
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1210_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_obj_once(&l_Lake_instReprElanInstall_repr___redArg___closed__22, &l_Lake_instReprElanInstall_repr___redArg___closed__22_once, _init_l_Lake_instReprElanInstall_repr___redArg___closed__22);
v___x_1219_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__23));
v___x_1220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1217_);
v___x_1221_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__24));
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1218_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*1, v___x_1154_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr(lean_object* v_x_1225_, lean_object* v_prec_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall_repr___boxed(lean_object* v_x_1228_, lean_object* v_prec_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lake_instReprLakeInstall_repr(v_x_1228_, v_prec_1229_);
lean_dec(v_prec_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib(lean_object* v_self_1233_){
_start:
{
lean_object* v_sharedDynlib_1234_; lean_object* v_path_1235_; 
v_sharedDynlib_1234_ = lean_ctor_get(v_self_1233_, 4);
v_path_1235_ = lean_ctor_get(v_sharedDynlib_1234_, 0);
lean_inc_ref(v_path_1235_);
return v_path_1235_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_sharedLib___boxed(lean_object* v_self_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lake_LakeInstall_sharedLib(v_self_1236_);
lean_dec_ref(v_self_1236_);
return v_res_1237_;
}
}
static lean_object* _init_l_Lake_LakeInstall_ofLean___closed__2(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = l_Lake_sharedLibExt;
v___x_1241_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__1));
v___x_1242_ = lean_string_append(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* v_lean_1244_){
_start:
{
lean_object* v_sysroot_1245_; lean_object* v_srcDir_1246_; lean_object* v_leanLibDir_1247_; lean_object* v_binDir_1248_; lean_object* v_sharedDynlibs_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___y_1253_; uint8_t v___x_1261_; 
v_sysroot_1245_ = lean_ctor_get(v_lean_1244_, 0);
lean_inc_ref(v_sysroot_1245_);
v_srcDir_1246_ = lean_ctor_get(v_lean_1244_, 2);
lean_inc_ref(v_srcDir_1246_);
v_leanLibDir_1247_ = lean_ctor_get(v_lean_1244_, 3);
lean_inc_ref(v_leanLibDir_1247_);
v_binDir_1248_ = lean_ctor_get(v_lean_1244_, 6);
lean_inc_ref(v_binDir_1248_);
v_sharedDynlibs_1249_ = lean_ctor_get(v_lean_1244_, 11);
lean_inc_ref(v_sharedDynlibs_1249_);
lean_dec_ref(v_lean_1244_);
v___x_1250_ = ((lean_object*)(l_Lake_lakeExe___closed__0));
v___x_1251_ = l_System_FilePath_join(v_srcDir_1246_, v___x_1250_);
v___x_1261_ = l_System_Platform_isWindows;
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_obj_once(&l_Lake_LakeInstall_ofLean___closed__2, &l_Lake_LakeInstall_ofLean___closed__2_once, _init_l_Lake_LakeInstall_ofLean___closed__2);
lean_inc_ref(v_leanLibDir_1247_);
v___x_1263_ = l_System_FilePath_join(v_leanLibDir_1247_, v___x_1262_);
v___y_1253_ = v___x_1263_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__3));
lean_inc_ref(v_binDir_1248_);
v___x_1265_ = l_System_FilePath_join(v_binDir_1248_, v___x_1264_);
v___y_1253_ = v___x_1265_;
goto v___jp_1252_;
}
v___jp_1252_:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1254_ = ((lean_object*)(l_Lake_LakeInstall_ofLean___closed__0));
v___x_1255_ = 0;
v___x_1256_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1257_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1257_, 0, v___y_1253_);
lean_ctor_set(v___x_1257_, 1, v___x_1254_);
lean_ctor_set(v___x_1257_, 2, v_sharedDynlibs_1249_);
lean_ctor_set(v___x_1257_, 3, v___x_1256_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*4, v___x_1255_);
v___x_1258_ = l_Lake_lakeExe;
lean_inc_ref(v_binDir_1248_);
v___x_1259_ = l_System_FilePath_join(v_binDir_1248_, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1260_, 0, v_sysroot_1245_);
lean_ctor_set(v___x_1260_, 1, v___x_1251_);
lean_ctor_set(v___x_1260_, 2, v_binDir_1248_);
lean_ctor_set(v___x_1260_, 3, v_leanLibDir_1247_);
lean_ctor_set(v___x_1260_, 4, v___x_1257_);
lean_ctor_set(v___x_1260_, 5, v___x_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__0));
v___x_1270_ = lean_io_getenv(v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1298_; 
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1298_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_val_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1298_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___y_1278_; 
v___x_1275_ = ((lean_object*)(l_Lake_findElanInstall_x3f___closed__1));
v___x_1276_ = lean_io_getenv(v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = ((lean_object*)(l_Lake_instReprElanInstall_repr___redArg___closed__12));
v___y_1278_ = v___x_1296_;
goto v___jp_1277_;
}
else
{
lean_object* v_val_1297_; 
v_val_1297_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___x_1276_, 1);
v___y_1278_ = v_val_1297_;
goto v___jp_1277_;
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_startInclusive_1283_; lean_object* v_endExclusive_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_string_utf8_byte_size(v___y_1278_);
lean_inc_ref(v___y_1278_);
v___x_1281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1278_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_ctor_set(v___x_1281_, 2, v___x_1280_);
v___x_1282_ = l_String_Slice_trimAscii(v___x_1281_);
v_startInclusive_1283_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_startInclusive_1283_);
v_endExclusive_1284_ = lean_ctor_get(v___x_1282_, 2);
lean_inc(v_endExclusive_1284_);
lean_dec_ref(v___x_1282_);
v___x_1285_ = lean_nat_sub(v_endExclusive_1284_, v_startInclusive_1283_);
lean_dec(v_startInclusive_1283_);
lean_dec(v_endExclusive_1284_);
v___x_1286_ = lean_nat_dec_eq(v___x_1285_, v___x_1279_);
lean_dec(v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1287_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
lean_inc_n(v_val_1271_, 2);
v___x_1288_ = l_System_FilePath_join(v_val_1271_, v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__3));
v___x_1290_ = l_System_FilePath_join(v_val_1271_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1291_, 0, v_val_1271_);
lean_ctor_set(v___x_1291_, 1, v___y_1278_);
lean_ctor_set(v___x_1291_, 2, v___x_1288_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1291_);
v___x_1293_ = v___x_1273_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1295_; 
lean_dec_ref(v___y_1278_);
lean_del_object(v___x_1273_);
lean_dec(v_val_1271_);
v___x_1295_ = lean_box(0);
return v___x_1295_;
}
}
}
}
else
{
lean_object* v___x_1299_; 
lean_dec(v___x_1270_);
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f___boxed(lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lake_findElanInstall_x3f();
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* v_lean_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1313_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1314_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__2));
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1318_ = 1;
v___x_1319_ = 0;
v___x_1320_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1320_, 0, v___x_1313_);
lean_ctor_set(v___x_1320_, 1, v_lean_1311_);
lean_ctor_set(v___x_1320_, 2, v___x_1314_);
lean_ctor_set(v___x_1320_, 3, v___x_1315_);
lean_ctor_set(v___x_1320_, 4, v___x_1317_);
lean_ctor_set_uint8(v___x_1320_, sizeof(void*)*5, v___x_1318_);
lean_ctor_set_uint8(v___x_1320_, sizeof(void*)*5 + 1, v___x_1319_);
v___x_1321_ = l_IO_Process_output(v___x_1320_, v___x_1315_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1340_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1340_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1340_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint32_t v_exitCode_1326_; lean_object* v_stdout_1327_; uint32_t v___x_1328_; uint8_t v___x_1329_; 
v_exitCode_1326_ = lean_ctor_get_uint32(v_a_1322_, sizeof(void*)*2);
v_stdout_1327_ = lean_ctor_get(v_a_1322_, 0);
lean_inc_ref(v_stdout_1327_);
lean_dec(v_a_1322_);
v___x_1328_ = 0;
v___x_1329_ = lean_uint32_dec_eq(v_exitCode_1326_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v_stdout_1327_);
lean_del_object(v___x_1324_);
return v___x_1315_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_str_1333_; lean_object* v_startInclusive_1334_; lean_object* v_endExclusive_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1330_ = lean_string_utf8_byte_size(v_stdout_1327_);
v___x_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1331_, 0, v_stdout_1327_);
lean_ctor_set(v___x_1331_, 1, v___x_1316_);
lean_ctor_set(v___x_1331_, 2, v___x_1330_);
v___x_1332_ = l_String_Slice_trimAscii(v___x_1331_);
v_str_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_ref(v_str_1333_);
v_startInclusive_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_startInclusive_1334_);
v_endExclusive_1335_ = lean_ctor_get(v___x_1332_, 2);
lean_inc(v_endExclusive_1335_);
lean_dec_ref(v___x_1332_);
v___x_1336_ = lean_string_utf8_extract(v_str_1333_, v_startInclusive_1334_, v_endExclusive_1335_);
lean_dec(v_endExclusive_1335_);
lean_dec(v_startInclusive_1334_);
lean_dec_ref(v_str_1333_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set_tag(v___x_1324_, 1);
lean_ctor_set(v___x_1324_, 0, v___x_1336_);
v___x_1338_ = v___x_1324_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1321_, 1);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f___boxed(lean_object* v_lean_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lake_findLeanSysroot_x3f(v_lean_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(lean_object* v_sysroot_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1351_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__0));
v___x_1352_ = l_Lake_leanExe(v_sysroot_1349_);
v___x_1353_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1));
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = ((lean_object*)(l_Lake_findLeanSysroot_x3f___closed__3));
v___x_1357_ = 1;
v___x_1358_ = 0;
v___x_1359_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1359_, 0, v___x_1351_);
lean_ctor_set(v___x_1359_, 1, v___x_1352_);
lean_ctor_set(v___x_1359_, 2, v___x_1353_);
lean_ctor_set(v___x_1359_, 3, v___x_1354_);
lean_ctor_set(v___x_1359_, 4, v___x_1356_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5, v___x_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5 + 1, v___x_1358_);
v___x_1360_ = l_IO_Process_output(v___x_1359_, v___x_1354_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_stdout_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_str_1366_; lean_object* v_startInclusive_1367_; lean_object* v_endExclusive_1368_; lean_object* v___x_1369_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_stdout_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc_ref(v_stdout_1362_);
lean_dec(v_a_1361_);
v___x_1363_ = lean_string_utf8_byte_size(v_stdout_1362_);
v___x_1364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1364_, 0, v_stdout_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1355_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
v___x_1365_ = l_String_Slice_trimAscii(v___x_1364_);
v_str_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc_ref(v_str_1366_);
v_startInclusive_1367_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_startInclusive_1367_);
v_endExclusive_1368_ = lean_ctor_get(v___x_1365_, 2);
lean_inc(v_endExclusive_1368_);
lean_dec_ref(v___x_1365_);
v___x_1369_ = lean_string_utf8_extract(v_str_1366_, v_startInclusive_1367_, v_endExclusive_1368_);
lean_dec(v_endExclusive_1368_);
lean_dec(v_startInclusive_1367_);
lean_dec_ref(v_str_1366_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; 
lean_dec_ref_known(v___x_1360_, 1);
v___x_1370_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(lean_object* v_sysroot_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(lean_object* v_sysroot_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0));
v___x_1379_ = lean_io_getenv(v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 1)
{
lean_object* v_val_1380_; 
lean_dec_ref(v_sysroot_1376_);
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v___x_1379_, 1);
return v_val_1380_;
}
else
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
lean_dec(v___x_1379_);
v___x_1381_ = l_Lake_leanArExe(v_sysroot_1376_);
v___x_1382_ = l_System_FilePath_pathExists(v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v___x_1381_);
v___x_1383_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1));
v___x_1384_ = lean_io_getenv(v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 1)
{
lean_object* v_val_1385_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
return v_val_1385_;
}
else
{
lean_object* v___x_1386_; 
lean_dec(v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
return v___x_1386_;
}
}
else
{
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(lean_object* v_sysroot_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(lean_object* v_sysroot_1390_, lean_object* v_i_1391_, lean_object* v_cc_1392_){
_start:
{
lean_object* v_sysroot_1393_; lean_object* v_githash_1394_; lean_object* v_srcDir_1395_; lean_object* v_leanLibDir_1396_; lean_object* v_includeDir_1397_; lean_object* v_systemLibDir_1398_; lean_object* v_binDir_1399_; lean_object* v_lean_1400_; lean_object* v_leanir_1401_; lean_object* v_leanc_1402_; lean_object* v_leantar_1403_; lean_object* v_sharedDynlibs_1404_; lean_object* v_sharedDynlib_1405_; lean_object* v_ar_1406_; lean_object* v_cFlags_1407_; lean_object* v_linkStaticFlags_1408_; lean_object* v_linkSharedFlags_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1422_; 
v_sysroot_1393_ = lean_ctor_get(v_i_1391_, 0);
v_githash_1394_ = lean_ctor_get(v_i_1391_, 1);
v_srcDir_1395_ = lean_ctor_get(v_i_1391_, 2);
v_leanLibDir_1396_ = lean_ctor_get(v_i_1391_, 3);
v_includeDir_1397_ = lean_ctor_get(v_i_1391_, 4);
v_systemLibDir_1398_ = lean_ctor_get(v_i_1391_, 5);
v_binDir_1399_ = lean_ctor_get(v_i_1391_, 6);
v_lean_1400_ = lean_ctor_get(v_i_1391_, 7);
v_leanir_1401_ = lean_ctor_get(v_i_1391_, 8);
v_leanc_1402_ = lean_ctor_get(v_i_1391_, 9);
v_leantar_1403_ = lean_ctor_get(v_i_1391_, 10);
v_sharedDynlibs_1404_ = lean_ctor_get(v_i_1391_, 11);
v_sharedDynlib_1405_ = lean_ctor_get(v_i_1391_, 12);
v_ar_1406_ = lean_ctor_get(v_i_1391_, 13);
v_cFlags_1407_ = lean_ctor_get(v_i_1391_, 15);
v_linkStaticFlags_1408_ = lean_ctor_get(v_i_1391_, 16);
v_linkSharedFlags_1409_ = lean_ctor_get(v_i_1391_, 17);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_i_1391_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; 
v_unused_1423_ = lean_ctor_get(v_i_1391_, 20);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_i_1391_, 19);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_i_1391_, 18);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_i_1391_, 14);
lean_dec(v_unused_1426_);
v___x_1411_ = v_i_1391_;
v_isShared_1412_ = v_isSharedCheck_1422_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_linkSharedFlags_1409_);
lean_inc(v_linkStaticFlags_1408_);
lean_inc(v_cFlags_1407_);
lean_inc(v_ar_1406_);
lean_inc(v_sharedDynlib_1405_);
lean_inc(v_sharedDynlibs_1404_);
lean_inc(v_leantar_1403_);
lean_inc(v_leanc_1402_);
lean_inc(v_leanir_1401_);
lean_inc(v_lean_1400_);
lean_inc(v_binDir_1399_);
lean_inc(v_systemLibDir_1398_);
lean_inc(v_includeDir_1397_);
lean_inc(v_leanLibDir_1396_);
lean_inc(v_srcDir_1395_);
lean_inc(v_githash_1394_);
lean_inc(v_sysroot_1393_);
lean_dec(v_i_1391_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1422_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_ccLinkFlags_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v_ccLinkFlags_1413_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_1390_);
v___x_1414_ = 0;
v___x_1415_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_1390_);
lean_inc_ref(v_cFlags_1407_);
v___x_1416_ = l_Array_append___redArg(v_cFlags_1407_, v___x_1415_);
lean_dec_ref(v___x_1415_);
lean_inc_ref(v_ccLinkFlags_1413_);
v___x_1417_ = l_Array_append___redArg(v_ccLinkFlags_1413_, v_linkStaticFlags_1408_);
v___x_1418_ = l_Array_append___redArg(v_ccLinkFlags_1413_, v_linkSharedFlags_1409_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 20, v___x_1418_);
lean_ctor_set(v___x_1411_, 19, v___x_1417_);
lean_ctor_set(v___x_1411_, 18, v___x_1416_);
lean_ctor_set(v___x_1411_, 14, v_cc_1392_);
v___x_1420_ = v___x_1411_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_sysroot_1393_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_githash_1394_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_srcDir_1395_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_leanLibDir_1396_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_includeDir_1397_);
lean_ctor_set(v_reuseFailAlloc_1421_, 5, v_systemLibDir_1398_);
lean_ctor_set(v_reuseFailAlloc_1421_, 6, v_binDir_1399_);
lean_ctor_set(v_reuseFailAlloc_1421_, 7, v_lean_1400_);
lean_ctor_set(v_reuseFailAlloc_1421_, 8, v_leanir_1401_);
lean_ctor_set(v_reuseFailAlloc_1421_, 9, v_leanc_1402_);
lean_ctor_set(v_reuseFailAlloc_1421_, 10, v_leantar_1403_);
lean_ctor_set(v_reuseFailAlloc_1421_, 11, v_sharedDynlibs_1404_);
lean_ctor_set(v_reuseFailAlloc_1421_, 12, v_sharedDynlib_1405_);
lean_ctor_set(v_reuseFailAlloc_1421_, 13, v_ar_1406_);
lean_ctor_set(v_reuseFailAlloc_1421_, 14, v_cc_1392_);
lean_ctor_set(v_reuseFailAlloc_1421_, 15, v_cFlags_1407_);
lean_ctor_set(v_reuseFailAlloc_1421_, 16, v_linkStaticFlags_1408_);
lean_ctor_set(v_reuseFailAlloc_1421_, 17, v_linkSharedFlags_1409_);
lean_ctor_set(v_reuseFailAlloc_1421_, 18, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1421_, 19, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1421_, 20, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*21, v___x_1414_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(lean_object* v_sysroot_1427_, lean_object* v_i_1428_, lean_object* v_cc_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1427_, v_i_1428_, v_cc_1429_);
lean_dec_ref(v_sysroot_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(lean_object* v_i_1431_, lean_object* v_cc_1432_){
_start:
{
lean_object* v_sysroot_1433_; lean_object* v_githash_1434_; lean_object* v_srcDir_1435_; lean_object* v_leanLibDir_1436_; lean_object* v_includeDir_1437_; lean_object* v_systemLibDir_1438_; lean_object* v_binDir_1439_; lean_object* v_lean_1440_; lean_object* v_leanir_1441_; lean_object* v_leanc_1442_; lean_object* v_leantar_1443_; lean_object* v_sharedDynlibs_1444_; lean_object* v_sharedDynlib_1445_; lean_object* v_ar_1446_; uint8_t v_customCc_1447_; lean_object* v_cFlags_1448_; lean_object* v_linkStaticFlags_1449_; lean_object* v_linkSharedFlags_1450_; lean_object* v_ccFlags_1451_; lean_object* v_ccLinkStaticFlags_1452_; lean_object* v_ccLinkSharedFlags_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
v_sysroot_1433_ = lean_ctor_get(v_i_1431_, 0);
v_githash_1434_ = lean_ctor_get(v_i_1431_, 1);
v_srcDir_1435_ = lean_ctor_get(v_i_1431_, 2);
v_leanLibDir_1436_ = lean_ctor_get(v_i_1431_, 3);
v_includeDir_1437_ = lean_ctor_get(v_i_1431_, 4);
v_systemLibDir_1438_ = lean_ctor_get(v_i_1431_, 5);
v_binDir_1439_ = lean_ctor_get(v_i_1431_, 6);
v_lean_1440_ = lean_ctor_get(v_i_1431_, 7);
v_leanir_1441_ = lean_ctor_get(v_i_1431_, 8);
v_leanc_1442_ = lean_ctor_get(v_i_1431_, 9);
v_leantar_1443_ = lean_ctor_get(v_i_1431_, 10);
v_sharedDynlibs_1444_ = lean_ctor_get(v_i_1431_, 11);
v_sharedDynlib_1445_ = lean_ctor_get(v_i_1431_, 12);
v_ar_1446_ = lean_ctor_get(v_i_1431_, 13);
v_customCc_1447_ = lean_ctor_get_uint8(v_i_1431_, sizeof(void*)*21);
v_cFlags_1448_ = lean_ctor_get(v_i_1431_, 15);
v_linkStaticFlags_1449_ = lean_ctor_get(v_i_1431_, 16);
v_linkSharedFlags_1450_ = lean_ctor_get(v_i_1431_, 17);
v_ccFlags_1451_ = lean_ctor_get(v_i_1431_, 18);
v_ccLinkStaticFlags_1452_ = lean_ctor_get(v_i_1431_, 19);
v_ccLinkSharedFlags_1453_ = lean_ctor_get(v_i_1431_, 20);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_i_1431_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_i_1431_, 14);
lean_dec(v_unused_1461_);
v___x_1455_ = v_i_1431_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1453_);
lean_inc(v_ccLinkStaticFlags_1452_);
lean_inc(v_ccFlags_1451_);
lean_inc(v_linkSharedFlags_1450_);
lean_inc(v_linkStaticFlags_1449_);
lean_inc(v_cFlags_1448_);
lean_inc(v_ar_1446_);
lean_inc(v_sharedDynlib_1445_);
lean_inc(v_sharedDynlibs_1444_);
lean_inc(v_leantar_1443_);
lean_inc(v_leanc_1442_);
lean_inc(v_leanir_1441_);
lean_inc(v_lean_1440_);
lean_inc(v_binDir_1439_);
lean_inc(v_systemLibDir_1438_);
lean_inc(v_includeDir_1437_);
lean_inc(v_leanLibDir_1436_);
lean_inc(v_srcDir_1435_);
lean_inc(v_githash_1434_);
lean_inc(v_sysroot_1433_);
lean_dec(v_i_1431_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 14, v_cc_1432_);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_sysroot_1433_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_githash_1434_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_srcDir_1435_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_leanLibDir_1436_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_includeDir_1437_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v_systemLibDir_1438_);
lean_ctor_set(v_reuseFailAlloc_1459_, 6, v_binDir_1439_);
lean_ctor_set(v_reuseFailAlloc_1459_, 7, v_lean_1440_);
lean_ctor_set(v_reuseFailAlloc_1459_, 8, v_leanir_1441_);
lean_ctor_set(v_reuseFailAlloc_1459_, 9, v_leanc_1442_);
lean_ctor_set(v_reuseFailAlloc_1459_, 10, v_leantar_1443_);
lean_ctor_set(v_reuseFailAlloc_1459_, 11, v_sharedDynlibs_1444_);
lean_ctor_set(v_reuseFailAlloc_1459_, 12, v_sharedDynlib_1445_);
lean_ctor_set(v_reuseFailAlloc_1459_, 13, v_ar_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 14, v_cc_1432_);
lean_ctor_set(v_reuseFailAlloc_1459_, 15, v_cFlags_1448_);
lean_ctor_set(v_reuseFailAlloc_1459_, 16, v_linkStaticFlags_1449_);
lean_ctor_set(v_reuseFailAlloc_1459_, 17, v_linkSharedFlags_1450_);
lean_ctor_set(v_reuseFailAlloc_1459_, 18, v_ccFlags_1451_);
lean_ctor_set(v_reuseFailAlloc_1459_, 19, v_ccLinkStaticFlags_1452_);
lean_ctor_set(v_reuseFailAlloc_1459_, 20, v_ccLinkSharedFlags_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*21, v_customCc_1447_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(lean_object* v_sysroot_1464_, lean_object* v_i_1465_){
_start:
{
lean_object* v_cc_1468_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0));
v___x_1499_ = lean_io_getenv(v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 1)
{
lean_object* v_val_1500_; 
lean_dec_ref(v_sysroot_1464_);
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_cc_1468_ = v_val_1500_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
lean_dec(v___x_1499_);
lean_inc_ref(v_sysroot_1464_);
v___x_1501_ = l_Lake_leanCcExe(v_sysroot_1464_);
v___x_1502_ = l_System_FilePath_pathExists(v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_sysroot_1464_);
v___x_1503_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1));
v___x_1504_ = lean_io_getenv(v___x_1503_);
if (lean_obj_tag(v___x_1504_) == 1)
{
lean_object* v_val_1505_; 
v_val_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v_cc_1468_ = v_val_1505_;
goto v___jp_1467_;
}
else
{
lean_object* v_sysroot_1506_; lean_object* v_githash_1507_; lean_object* v_srcDir_1508_; lean_object* v_leanLibDir_1509_; lean_object* v_includeDir_1510_; lean_object* v_systemLibDir_1511_; lean_object* v_binDir_1512_; lean_object* v_lean_1513_; lean_object* v_leanir_1514_; lean_object* v_leanc_1515_; lean_object* v_leantar_1516_; lean_object* v_sharedDynlibs_1517_; lean_object* v_sharedDynlib_1518_; lean_object* v_ar_1519_; uint8_t v_customCc_1520_; lean_object* v_cFlags_1521_; lean_object* v_linkStaticFlags_1522_; lean_object* v_linkSharedFlags_1523_; lean_object* v_ccFlags_1524_; lean_object* v_ccLinkStaticFlags_1525_; lean_object* v_ccLinkSharedFlags_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v___x_1504_);
v_sysroot_1506_ = lean_ctor_get(v_i_1465_, 0);
v_githash_1507_ = lean_ctor_get(v_i_1465_, 1);
v_srcDir_1508_ = lean_ctor_get(v_i_1465_, 2);
v_leanLibDir_1509_ = lean_ctor_get(v_i_1465_, 3);
v_includeDir_1510_ = lean_ctor_get(v_i_1465_, 4);
v_systemLibDir_1511_ = lean_ctor_get(v_i_1465_, 5);
v_binDir_1512_ = lean_ctor_get(v_i_1465_, 6);
v_lean_1513_ = lean_ctor_get(v_i_1465_, 7);
v_leanir_1514_ = lean_ctor_get(v_i_1465_, 8);
v_leanc_1515_ = lean_ctor_get(v_i_1465_, 9);
v_leantar_1516_ = lean_ctor_get(v_i_1465_, 10);
v_sharedDynlibs_1517_ = lean_ctor_get(v_i_1465_, 11);
v_sharedDynlib_1518_ = lean_ctor_get(v_i_1465_, 12);
v_ar_1519_ = lean_ctor_get(v_i_1465_, 13);
v_customCc_1520_ = lean_ctor_get_uint8(v_i_1465_, sizeof(void*)*21);
v_cFlags_1521_ = lean_ctor_get(v_i_1465_, 15);
v_linkStaticFlags_1522_ = lean_ctor_get(v_i_1465_, 16);
v_linkSharedFlags_1523_ = lean_ctor_get(v_i_1465_, 17);
v_ccFlags_1524_ = lean_ctor_get(v_i_1465_, 18);
v_ccLinkStaticFlags_1525_ = lean_ctor_get(v_i_1465_, 19);
v_ccLinkSharedFlags_1526_ = lean_ctor_get(v_i_1465_, 20);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_i_1465_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_i_1465_, 14);
lean_dec(v_unused_1535_);
v___x_1528_ = v_i_1465_;
v_isShared_1529_ = v_isSharedCheck_1534_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1526_);
lean_inc(v_ccLinkStaticFlags_1525_);
lean_inc(v_ccFlags_1524_);
lean_inc(v_linkSharedFlags_1523_);
lean_inc(v_linkStaticFlags_1522_);
lean_inc(v_cFlags_1521_);
lean_inc(v_ar_1519_);
lean_inc(v_sharedDynlib_1518_);
lean_inc(v_sharedDynlibs_1517_);
lean_inc(v_leantar_1516_);
lean_inc(v_leanc_1515_);
lean_inc(v_leanir_1514_);
lean_inc(v_lean_1513_);
lean_inc(v_binDir_1512_);
lean_inc(v_systemLibDir_1511_);
lean_inc(v_includeDir_1510_);
lean_inc(v_leanLibDir_1509_);
lean_inc(v_srcDir_1508_);
lean_inc(v_githash_1507_);
lean_inc(v_sysroot_1506_);
lean_dec(v_i_1465_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1534_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 14, v___x_1530_);
v___x_1532_ = v___x_1528_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_sysroot_1506_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_githash_1507_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_srcDir_1508_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_leanLibDir_1509_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_includeDir_1510_);
lean_ctor_set(v_reuseFailAlloc_1533_, 5, v_systemLibDir_1511_);
lean_ctor_set(v_reuseFailAlloc_1533_, 6, v_binDir_1512_);
lean_ctor_set(v_reuseFailAlloc_1533_, 7, v_lean_1513_);
lean_ctor_set(v_reuseFailAlloc_1533_, 8, v_leanir_1514_);
lean_ctor_set(v_reuseFailAlloc_1533_, 9, v_leanc_1515_);
lean_ctor_set(v_reuseFailAlloc_1533_, 10, v_leantar_1516_);
lean_ctor_set(v_reuseFailAlloc_1533_, 11, v_sharedDynlibs_1517_);
lean_ctor_set(v_reuseFailAlloc_1533_, 12, v_sharedDynlib_1518_);
lean_ctor_set(v_reuseFailAlloc_1533_, 13, v_ar_1519_);
lean_ctor_set(v_reuseFailAlloc_1533_, 14, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1533_, 15, v_cFlags_1521_);
lean_ctor_set(v_reuseFailAlloc_1533_, 16, v_linkStaticFlags_1522_);
lean_ctor_set(v_reuseFailAlloc_1533_, 17, v_linkSharedFlags_1523_);
lean_ctor_set(v_reuseFailAlloc_1533_, 18, v_ccFlags_1524_);
lean_ctor_set(v_reuseFailAlloc_1533_, 19, v_ccLinkStaticFlags_1525_);
lean_ctor_set(v_reuseFailAlloc_1533_, 20, v_ccLinkSharedFlags_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1533_, sizeof(void*)*21, v_customCc_1520_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_1464_, v_i_1465_, v___x_1501_);
lean_dec_ref(v_sysroot_1464_);
return v___x_1536_;
}
}
v___jp_1467_:
{
lean_object* v_sysroot_1469_; lean_object* v_githash_1470_; lean_object* v_srcDir_1471_; lean_object* v_leanLibDir_1472_; lean_object* v_includeDir_1473_; lean_object* v_systemLibDir_1474_; lean_object* v_binDir_1475_; lean_object* v_lean_1476_; lean_object* v_leanir_1477_; lean_object* v_leanc_1478_; lean_object* v_leantar_1479_; lean_object* v_sharedDynlibs_1480_; lean_object* v_sharedDynlib_1481_; lean_object* v_ar_1482_; uint8_t v_customCc_1483_; lean_object* v_cFlags_1484_; lean_object* v_linkStaticFlags_1485_; lean_object* v_linkSharedFlags_1486_; lean_object* v_ccFlags_1487_; lean_object* v_ccLinkStaticFlags_1488_; lean_object* v_ccLinkSharedFlags_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_sysroot_1469_ = lean_ctor_get(v_i_1465_, 0);
v_githash_1470_ = lean_ctor_get(v_i_1465_, 1);
v_srcDir_1471_ = lean_ctor_get(v_i_1465_, 2);
v_leanLibDir_1472_ = lean_ctor_get(v_i_1465_, 3);
v_includeDir_1473_ = lean_ctor_get(v_i_1465_, 4);
v_systemLibDir_1474_ = lean_ctor_get(v_i_1465_, 5);
v_binDir_1475_ = lean_ctor_get(v_i_1465_, 6);
v_lean_1476_ = lean_ctor_get(v_i_1465_, 7);
v_leanir_1477_ = lean_ctor_get(v_i_1465_, 8);
v_leanc_1478_ = lean_ctor_get(v_i_1465_, 9);
v_leantar_1479_ = lean_ctor_get(v_i_1465_, 10);
v_sharedDynlibs_1480_ = lean_ctor_get(v_i_1465_, 11);
v_sharedDynlib_1481_ = lean_ctor_get(v_i_1465_, 12);
v_ar_1482_ = lean_ctor_get(v_i_1465_, 13);
v_customCc_1483_ = lean_ctor_get_uint8(v_i_1465_, sizeof(void*)*21);
v_cFlags_1484_ = lean_ctor_get(v_i_1465_, 15);
v_linkStaticFlags_1485_ = lean_ctor_get(v_i_1465_, 16);
v_linkSharedFlags_1486_ = lean_ctor_get(v_i_1465_, 17);
v_ccFlags_1487_ = lean_ctor_get(v_i_1465_, 18);
v_ccLinkStaticFlags_1488_ = lean_ctor_get(v_i_1465_, 19);
v_ccLinkSharedFlags_1489_ = lean_ctor_get(v_i_1465_, 20);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_i_1465_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_i_1465_, 14);
lean_dec(v_unused_1497_);
v___x_1491_ = v_i_1465_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_ccLinkSharedFlags_1489_);
lean_inc(v_ccLinkStaticFlags_1488_);
lean_inc(v_ccFlags_1487_);
lean_inc(v_linkSharedFlags_1486_);
lean_inc(v_linkStaticFlags_1485_);
lean_inc(v_cFlags_1484_);
lean_inc(v_ar_1482_);
lean_inc(v_sharedDynlib_1481_);
lean_inc(v_sharedDynlibs_1480_);
lean_inc(v_leantar_1479_);
lean_inc(v_leanc_1478_);
lean_inc(v_leanir_1477_);
lean_inc(v_lean_1476_);
lean_inc(v_binDir_1475_);
lean_inc(v_systemLibDir_1474_);
lean_inc(v_includeDir_1473_);
lean_inc(v_leanLibDir_1472_);
lean_inc(v_srcDir_1471_);
lean_inc(v_githash_1470_);
lean_inc(v_sysroot_1469_);
lean_dec(v_i_1465_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 14, v_cc_1468_);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_sysroot_1469_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_githash_1470_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_srcDir_1471_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_leanLibDir_1472_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_includeDir_1473_);
lean_ctor_set(v_reuseFailAlloc_1495_, 5, v_systemLibDir_1474_);
lean_ctor_set(v_reuseFailAlloc_1495_, 6, v_binDir_1475_);
lean_ctor_set(v_reuseFailAlloc_1495_, 7, v_lean_1476_);
lean_ctor_set(v_reuseFailAlloc_1495_, 8, v_leanir_1477_);
lean_ctor_set(v_reuseFailAlloc_1495_, 9, v_leanc_1478_);
lean_ctor_set(v_reuseFailAlloc_1495_, 10, v_leantar_1479_);
lean_ctor_set(v_reuseFailAlloc_1495_, 11, v_sharedDynlibs_1480_);
lean_ctor_set(v_reuseFailAlloc_1495_, 12, v_sharedDynlib_1481_);
lean_ctor_set(v_reuseFailAlloc_1495_, 13, v_ar_1482_);
lean_ctor_set(v_reuseFailAlloc_1495_, 14, v_cc_1468_);
lean_ctor_set(v_reuseFailAlloc_1495_, 15, v_cFlags_1484_);
lean_ctor_set(v_reuseFailAlloc_1495_, 16, v_linkStaticFlags_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 17, v_linkSharedFlags_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 18, v_ccFlags_1487_);
lean_ctor_set(v_reuseFailAlloc_1495_, 19, v_ccLinkStaticFlags_1488_);
lean_ctor_set(v_reuseFailAlloc_1495_, 20, v_ccLinkSharedFlags_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1495_, sizeof(void*)*21, v_customCc_1483_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(lean_object* v_sysroot_1537_, lean_object* v_i_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1537_, v_i_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* v_sysroot_1541_, uint8_t v_collocated_1542_){
_start:
{
lean_object* v_githash_1545_; 
if (v_collocated_1542_ == 0)
{
lean_object* v___x_1571_; 
lean_inc_ref(v_sysroot_1541_);
v___x_1571_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_1541_);
v_githash_1545_ = v___x_1571_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_githash;
v_githash_1545_ = v___x_1572_;
goto v___jp_1544_;
}
v___jp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_inc_ref_n(v_sysroot_1541_, 12);
v___x_1546_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_1541_);
v___x_1547_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
v___x_1548_ = l_System_FilePath_join(v_sysroot_1541_, v___x_1547_);
v___x_1549_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1550_ = l_System_FilePath_join(v___x_1548_, v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1552_ = l_System_FilePath_join(v_sysroot_1541_, v___x_1551_);
lean_inc_ref(v___x_1552_);
v___x_1553_ = l_System_FilePath_join(v___x_1552_, v___x_1549_);
v___x_1554_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1555_ = l_System_FilePath_join(v_sysroot_1541_, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1557_ = l_System_FilePath_join(v_sysroot_1541_, v___x_1556_);
v___x_1558_ = l_Lake_leanExe(v_sysroot_1541_);
v___x_1559_ = l_Lake_leanirExe(v_sysroot_1541_);
v___x_1560_ = l_Lake_leancExe(v_sysroot_1541_);
v___x_1561_ = l_Lake_leantarExe(v_sysroot_1541_);
v___x_1562_ = l_Lake_leanSharedDynlibs(v_sysroot_1541_);
v___x_1563_ = l_Lake_leanSharedDynlib(v_sysroot_1541_);
v___x_1564_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1565_ = 1;
v___x_1566_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1567_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__17, &l_Lake_instInhabitedLeanInstall_default___closed__17_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__17);
v___x_1568_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
v___x_1569_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1569_, 0, v_sysroot_1541_);
lean_ctor_set(v___x_1569_, 1, v_githash_1545_);
lean_ctor_set(v___x_1569_, 2, v___x_1550_);
lean_ctor_set(v___x_1569_, 3, v___x_1553_);
lean_ctor_set(v___x_1569_, 4, v___x_1555_);
lean_ctor_set(v___x_1569_, 5, v___x_1552_);
lean_ctor_set(v___x_1569_, 6, v___x_1557_);
lean_ctor_set(v___x_1569_, 7, v___x_1558_);
lean_ctor_set(v___x_1569_, 8, v___x_1559_);
lean_ctor_set(v___x_1569_, 9, v___x_1560_);
lean_ctor_set(v___x_1569_, 10, v___x_1561_);
lean_ctor_set(v___x_1569_, 11, v___x_1562_);
lean_ctor_set(v___x_1569_, 12, v___x_1563_);
lean_ctor_set(v___x_1569_, 13, v___x_1546_);
lean_ctor_set(v___x_1569_, 14, v___x_1564_);
lean_ctor_set(v___x_1569_, 15, v___x_1566_);
lean_ctor_set(v___x_1569_, 16, v___x_1567_);
lean_ctor_set(v___x_1569_, 17, v___x_1568_);
lean_ctor_set(v___x_1569_, 18, v___x_1566_);
lean_ctor_set(v___x_1569_, 19, v___x_1567_);
lean_ctor_set(v___x_1569_, 20, v___x_1568_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*21, v___x_1565_);
v___x_1570_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(v_sysroot_1541_, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* v_sysroot_1573_, lean_object* v_collocated_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v_collocated_boxed_1576_; lean_object* v_res_1577_; 
v_collocated_boxed_1576_ = lean_unbox(v_collocated_1574_);
v_res_1577_ = l_Lake_LeanInstall_get(v_sysroot_1573_, v_collocated_boxed_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* v_lean_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lake_findLeanSysroot_x3f(v_lean_1578_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_box(0);
return v___x_1581_;
}
else
{
lean_object* v_val_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1591_; 
v_val_1582_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1584_ = v___x_1580_;
v_isShared_1585_ = v_isSharedCheck_1591_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_val_1582_);
lean_dec(v___x_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1591_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1586_ = 0;
v___x_1587_ = l_Lake_LeanInstall_get(v_val_1582_, v___x_1586_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1587_);
v___x_1589_ = v___x_1584_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f___boxed(lean_object* v_lean_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lake_findLeanCmdInstall_x3f(v_lean_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_io_app_path();
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = l_System_FilePath_parent(v_a_1599_);
if (lean_obj_tag(v___x_1600_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_val_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_n(v_val_1601_, 2);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1603_ = l_System_FilePath_join(v_val_1601_, v___x_1602_);
v___x_1604_ = l_System_FilePath_exeExtension;
v___x_1605_ = l_System_FilePath_addExtension(v___x_1603_, v___x_1604_);
v___x_1606_ = l_System_FilePath_pathExists(v___x_1605_);
lean_dec_ref(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_dec(v_val_1601_);
goto v___jp_1596_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = l_System_FilePath_parent(v_val_1601_);
return v___x_1607_;
}
}
else
{
lean_dec(v___x_1600_);
goto v___jp_1596_;
}
}
else
{
lean_dec_ref_known(v___x_1598_, 1);
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_box(0);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f___boxed(lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lake_findLakeLeanJointHome_x3f();
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* v_lake_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_System_FilePath_parent(v_lake_1610_);
if (lean_obj_tag(v___x_1611_) == 0)
{
return v___x_1611_;
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1613_; 
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = l_System_FilePath_parent(v_val_1612_);
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
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* v_lake_1619_){
_start:
{
lean_object* v___x_1621_; 
lean_inc_ref(v_lake_1619_);
v___x_1621_ = l_Lake_lakeBuildHome_x3f(v_lake_1619_);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1646_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1646_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1646_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_lake_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1626_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1622_, 2);
v___x_1627_ = l_System_FilePath_join(v_val_1622_, v___x_1626_);
v___x_1628_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1627_);
v___x_1629_ = l_System_FilePath_join(v___x_1627_, v___x_1628_);
v___x_1630_ = l_Lake_defaultLeanLibDir;
v___x_1631_ = l_System_FilePath_join(v___x_1627_, v___x_1630_);
v___x_1632_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1633_ = 0;
v___x_1634_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref_n(v___x_1631_, 2);
v___x_1635_ = l_System_FilePath_join(v___x_1631_, v___x_1634_);
v___x_1636_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1637_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1632_);
lean_ctor_set(v___x_1637_, 2, v___x_1636_);
lean_ctor_set(v___x_1637_, 3, v___x_1636_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*4, v___x_1633_);
v_lake_1638_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_lake_1638_, 0, v_val_1622_);
lean_ctor_set(v_lake_1638_, 1, v_val_1622_);
lean_ctor_set(v_lake_1638_, 2, v___x_1629_);
lean_ctor_set(v_lake_1638_, 3, v___x_1631_);
lean_ctor_set(v_lake_1638_, 4, v___x_1637_);
lean_ctor_set(v_lake_1638_, 5, v_lake_1619_);
v___x_1639_ = ((lean_object*)(l_Lake_getLakeInstall_x3f___closed__0));
v___x_1640_ = l_System_FilePath_join(v___x_1631_, v___x_1639_);
v___x_1641_ = l_System_FilePath_pathExists(v___x_1640_);
lean_dec_ref(v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; 
lean_dec_ref_known(v_lake_1638_, 6);
lean_del_object(v___x_1624_);
v___x_1642_ = lean_box(0);
return v___x_1642_;
}
else
{
lean_object* v___x_1644_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_lake_1638_);
v___x_1644_ = v___x_1624_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_lake_1638_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v___x_1647_; 
lean_dec(v___x_1621_);
lean_dec_ref(v_lake_1619_);
v___x_1647_ = lean_box(0);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f___boxed(lean_object* v_lake_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lake_getLakeInstall_x3f(v_lake_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__0));
v___x_1655_ = lean_io_getenv(v___x_1654_);
if (lean_obj_tag(v___x_1655_) == 1)
{
lean_object* v_val_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1665_; 
v_val_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_val_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
uint8_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1660_ = 0;
v___x_1661_ = l_Lake_LeanInstall_get(v_val_1656_, v___x_1660_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v_lean_1669_; 
lean_dec(v___x_1655_);
v___x_1666_ = ((lean_object*)(l_Lake_findLeanInstall_x3f___closed__1));
v___x_1667_ = lean_io_getenv(v___x_1666_);
if (lean_obj_tag(v___x_1667_) == 1)
{
lean_object* v_val_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v_startInclusive_1687_; lean_object* v_endExclusive_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_val_1682_ = lean_ctor_get(v___x_1667_, 0);
lean_inc_n(v_val_1682_, 2);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_string_utf8_byte_size(v_val_1682_);
v___x_1685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1685_, 0, v_val_1682_);
lean_ctor_set(v___x_1685_, 1, v___x_1683_);
lean_ctor_set(v___x_1685_, 2, v___x_1684_);
v___x_1686_ = l_String_Slice_trimAscii(v___x_1685_);
v_startInclusive_1687_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_startInclusive_1687_);
v_endExclusive_1688_ = lean_ctor_get(v___x_1686_, 2);
lean_inc(v_endExclusive_1688_);
lean_dec_ref(v___x_1686_);
v___x_1689_ = lean_nat_sub(v_endExclusive_1688_, v_startInclusive_1687_);
lean_dec(v_startInclusive_1687_);
lean_dec(v_endExclusive_1688_);
v___x_1690_ = lean_nat_dec_eq(v___x_1689_, v___x_1683_);
lean_dec(v___x_1689_);
if (v___x_1690_ == 0)
{
v_lean_1669_ = v_val_1682_;
goto v___jp_1668_;
}
else
{
lean_object* v___x_1691_; 
lean_dec(v_val_1682_);
v___x_1691_ = lean_box(0);
return v___x_1691_;
}
}
else
{
lean_object* v___x_1692_; 
lean_dec(v___x_1667_);
v___x_1692_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v_lean_1669_ = v___x_1692_;
goto v___jp_1668_;
}
v___jp_1668_:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lake_findLeanSysroot_x3f(v_lean_1669_);
if (lean_obj_tag(v___x_1670_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1680_; 
v_val_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = 0;
v___x_1676_ = l_Lake_LeanInstall_get(v_val_1671_, v___x_1675_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v___x_1681_; 
lean_dec(v___x_1670_);
v___x_1681_ = lean_box(0);
return v___x_1681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f___boxed(lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lake_findLeanInstall_x3f();
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_io_app_path();
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lake_getLakeInstall_x3f(v_a_1725_);
if (lean_obj_tag(v___x_1726_) == 1)
{
return v___x_1726_;
}
else
{
lean_dec(v___x_1726_);
goto v___jp_1697_;
}
}
else
{
lean_dec_ref_known(v___x_1724_, 1);
goto v___jp_1697_;
}
v___jp_1697_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lake_findLakeInstall_x3f___closed__0));
v___x_1699_ = lean_io_getenv(v___x_1698_);
if (lean_obj_tag(v___x_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1722_; 
v_val_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1722_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_val_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1722_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1704_ = l_Lake_defaultBuildDir;
lean_inc_n(v_val_1700_, 2);
v___x_1705_ = l_System_FilePath_join(v_val_1700_, v___x_1704_);
v___x_1706_ = l_Lake_defaultBinDir;
lean_inc_ref(v___x_1705_);
v___x_1707_ = l_System_FilePath_join(v___x_1705_, v___x_1706_);
v___x_1708_ = l_Lake_defaultLeanLibDir;
v___x_1709_ = l_System_FilePath_join(v___x_1705_, v___x_1708_);
v___x_1710_ = ((lean_object*)(l_Lake_instInhabitedLakeInstall_default___closed__3));
v___x_1711_ = 0;
v___x_1712_ = lean_obj_once(&l_Lake_instInhabitedLakeInstall_default___closed__4, &l_Lake_instInhabitedLakeInstall_default___closed__4_once, _init_l_Lake_instInhabitedLakeInstall_default___closed__4);
lean_inc_ref(v___x_1709_);
v___x_1713_ = l_System_FilePath_join(v___x_1709_, v___x_1712_);
v___x_1714_ = ((lean_object*)(l___private_Lake_Config_InstallPath_0__Lake_leanSharedDynlibs_winLib___closed__1));
v___x_1715_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1710_);
lean_ctor_set(v___x_1715_, 2, v___x_1714_);
lean_ctor_set(v___x_1715_, 3, v___x_1714_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*4, v___x_1711_);
v___x_1716_ = l_Lake_lakeExe;
lean_inc_ref(v___x_1707_);
v___x_1717_ = l_System_FilePath_join(v___x_1707_, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1718_, 0, v_val_1700_);
lean_ctor_set(v___x_1718_, 1, v_val_1700_);
lean_ctor_set(v___x_1718_, 2, v___x_1707_);
lean_ctor_set(v___x_1718_, 3, v___x_1709_);
lean_ctor_set(v___x_1718_, 4, v___x_1715_);
lean_ctor_set(v___x_1718_, 5, v___x_1717_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1718_);
v___x_1720_ = v___x_1702_;
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
lean_object* v___x_1723_; 
lean_dec(v___x_1699_);
v___x_1723_ = lean_box(0);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f___boxed(lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lake_findLakeInstall_x3f();
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = l_Lake_findElanInstall_x3f();
v___x_1732_ = l_Lake_findLakeLeanJointHome_x3f();
if (lean_obj_tag(v___x_1732_) == 1)
{
lean_object* v_val_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1790_; 
v_val_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1790_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_val_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1790_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lake_findInstall_x3f___closed__0));
v___x_1738_ = lean_io_getenv(v___x_1737_);
if (lean_obj_tag(v___x_1738_) == 0)
{
goto v___jp_1739_;
}
else
{
lean_object* v_val_1749_; lean_object* v___x_1750_; 
v_val_1749_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_val_1749_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1750_ = l_Lake_envToBool_x3f(v_val_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
goto v___jp_1739_;
}
else
{
lean_object* v_val_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1789_; 
v_val_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1789_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_val_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1789_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_unbox(v_val_1751_);
if (v___x_1755_ == 0)
{
lean_del_object(v___x_1753_);
lean_dec(v_val_1751_);
goto v___jp_1739_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
lean_del_object(v___x_1735_);
v___x_1756_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__0));
v___x_1757_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__0));
lean_inc_n(v_val_1733_, 10);
v___x_1758_ = l_System_FilePath_join(v_val_1733_, v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lake_leanExe___closed__0));
v___x_1760_ = l_System_FilePath_join(v___x_1758_, v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Lake_leanSharedLibDir___closed__0));
v___x_1762_ = l_System_FilePath_join(v_val_1733_, v___x_1761_);
lean_inc_ref(v___x_1762_);
v___x_1763_ = l_System_FilePath_join(v___x_1762_, v___x_1759_);
v___x_1764_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__5));
v___x_1765_ = l_System_FilePath_join(v_val_1733_, v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Lake_instInhabitedElanInstall_default___closed__1));
v___x_1767_ = l_System_FilePath_join(v_val_1733_, v___x_1766_);
v___x_1768_ = l_Lake_leanExe(v_val_1733_);
v___x_1769_ = l_Lake_leanirExe(v_val_1733_);
v___x_1770_ = l_Lake_leancExe(v_val_1733_);
v___x_1771_ = l_Lake_leantarExe(v_val_1733_);
v___x_1772_ = l_Lake_leanSharedDynlibs(v_val_1733_);
v___x_1773_ = l_Lake_leanSharedDynlib(v_val_1733_);
v___x_1774_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__13));
v___x_1775_ = ((lean_object*)(l_Lake_instInhabitedLeanInstall_default___closed__14));
v___x_1776_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__16, &l_Lake_instInhabitedLeanInstall_default___closed__16_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__16);
v___x_1777_ = lean_unbox(v_val_1751_);
v___x_1778_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1777_);
v___x_1779_ = lean_obj_once(&l_Lake_instInhabitedLeanInstall_default___closed__18, &l_Lake_instInhabitedLeanInstall_default___closed__18_once, _init_l_Lake_instInhabitedLeanInstall_default___closed__18);
lean_inc_ref(v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(v___x_1780_, 0, v_val_1733_);
lean_ctor_set(v___x_1780_, 1, v___x_1756_);
lean_ctor_set(v___x_1780_, 2, v___x_1760_);
lean_ctor_set(v___x_1780_, 3, v___x_1763_);
lean_ctor_set(v___x_1780_, 4, v___x_1765_);
lean_ctor_set(v___x_1780_, 5, v___x_1762_);
lean_ctor_set(v___x_1780_, 6, v___x_1767_);
lean_ctor_set(v___x_1780_, 7, v___x_1768_);
lean_ctor_set(v___x_1780_, 8, v___x_1769_);
lean_ctor_set(v___x_1780_, 9, v___x_1770_);
lean_ctor_set(v___x_1780_, 10, v___x_1771_);
lean_ctor_set(v___x_1780_, 11, v___x_1772_);
lean_ctor_set(v___x_1780_, 12, v___x_1773_);
lean_ctor_set(v___x_1780_, 13, v___x_1774_);
lean_ctor_set(v___x_1780_, 14, v___x_1775_);
lean_ctor_set(v___x_1780_, 15, v___x_1776_);
lean_ctor_set(v___x_1780_, 16, v___x_1778_);
lean_ctor_set(v___x_1780_, 17, v___x_1779_);
lean_ctor_set(v___x_1780_, 18, v___x_1776_);
lean_ctor_set(v___x_1780_, 19, v___x_1778_);
lean_ctor_set(v___x_1780_, 20, v___x_1779_);
v___x_1781_ = lean_unbox(v_val_1751_);
lean_dec(v_val_1751_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*21, v___x_1781_);
v___x_1782_ = l_Lake_findLeanInstall_x3f();
v___x_1783_ = l_Lake_LakeInstall_ofLean(v___x_1780_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1783_);
v___x_1785_ = v___x_1753_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1782_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1731_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
return v___x_1787_;
}
}
}
}
}
v___jp_1739_:
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1740_ = 1;
v___x_1741_ = l_Lake_LeanInstall_get(v_val_1733_, v___x_1740_);
lean_inc_ref(v___x_1741_);
v___x_1742_ = l_Lake_LakeInstall_ofLean(v___x_1741_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1741_);
v___x_1744_ = v___x_1735_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1741_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1742_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1731_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v___x_1732_);
v___x_1791_ = l_Lake_findLeanInstall_x3f();
v___x_1792_ = l_Lake_findLakeInstall_x3f();
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1731_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f___boxed(lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lake_findInstall_x3f();
return v_res_1796_;
}
}
lean_object* runtime_initialize_Lean_Compiler_FFI(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
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
