// Lean compiler output
// Module: Lake.CLI.Init
// Imports: public import Lake.Config.Env public import Lake.Config.Lang import Lake.Util.Git import Lake.Load.Workspace import Init.Data.String.Modify
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
extern uint32_t l_Lean_idEndEscape;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
extern lean_object* l_Lake_toolchainFileName;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_Git_upstreamBranch;
lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lake_ToolchainVer_ofString(lean_object*);
lean_object* l_Lake_toUpperCamelCase(lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static const lean_string_object l_Lake_defaultExeRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l_Lake_defaultExeRoot___closed__0 = (const lean_object*)&l_Lake_defaultExeRoot___closed__0_value;
static const lean_ctor_object l_Lake_defaultExeRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_defaultExeRoot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 217, 115, 245, 30, 114, 54, 221)}};
static const lean_object* l_Lake_defaultExeRoot___closed__1 = (const lean_object*)&l_Lake_defaultExeRoot___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_defaultExeRoot = (const lean_object*)&l_Lake_defaultExeRoot___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "def hello := \"world\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "-- This module serves as the root of the `"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "` library.\n-- Import modules here that should be built as part of the library.\nimport "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".Basic\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "def main : IO Unit :=\n  IO.println s!\"Hello, world!\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_exeFileContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "import Lake\nopen Lake DSL\n\npackage "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = " where\n  version := v!\"0.1.0\"\n\nlean_lib "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = " where\n  -- add library configuration options here\n\n@[default_target]\nlean_exe "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " where\n  root := `Main\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "name = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "\nversion = \"0.1.0\"\ndefaultTargets = ["};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "]\n\n[[lean_lib]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\n\n[[lean_exe]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nroot = \"Main\"\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = " where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_exe "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "]\n\n[[lean_exe]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = " where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_lib "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = " where\n  -- add library configuration options here\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 192, .m_capacity = 192, .m_length = 185, .m_data = " where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\" @ git "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "\n\n@[default_target]\nlean_lib "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = " where\n  -- add any library configuration options here\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "\nversion = \"0.1.0\"\nkeywords = [\"math\"]\ndefaultTargets = ["};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 134, .m_data = "]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\nrev = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\n\n[[lean_lib]]\nname = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 324, .m_capacity = 324, .m_length = 305, .m_data = " where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`\n    ⟨`relaxedAutoImplicit, false⟩,\n    ⟨`maxSynthPendingDepth, .ofNat 3⟩,\n    ⟨`weak.linter.mathlibStandardSet, true⟩,\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\" @ git "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 228, .m_capacity = 228, .m_length = 225, .m_data = "]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\nrelaxedAutoImplicit = false\nweak.linter.mathlibStandardSet = true\nmaxSynthPendingDepth = 3\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\nrev = "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "# "};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 476, .m_capacity = 476, .m_length = 475, .m_data = "\n\n## GitHub configuration\n\nTo set up your new GitHub repository, follow these steps:\n\n* Under your repository name, click **Settings**.\n* In the **Actions** section of the sidebar, click \"General\".\n* Check the box **Allow GitHub Actions to create and approve pull requests**.\n* Click the **Pages** section of the settings sidebar.\n* In the **Source** dropdown menu, select \"GitHub Actions\".\n\nAfter following the steps above, you can remove this section from the README file.\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 201, .m_capacity = 201, .m_length = 200, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v7\n      - uses: leanprover/lean-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 488, .m_capacity = 488, .m_length = 487, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\n# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages\npermissions:\n  contents: read # Read access to repository contents\n  pages: write # Write access to GitHub Pages\n  id-token: write # Write access to ID tokens\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v7\n      - uses: leanprover/lean-action@v1\n      - uses: leanprover-community/docgen-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1951, .m_capacity = 1951, .m_length = 1950, .m_data = "name: Update Dependencies\n\non:\n  # schedule:             # Sets a schedule to trigger the workflow\n  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)\n  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface\n\njobs:\n  check-for-updates: # Determines which updates to apply.\n    runs-on: ubuntu-latest\n    outputs:\n      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}\n      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}\n    steps:\n      - name: Run the action\n        id: check-for-updates\n        uses: leanprover-community/mathlib-update-action@v1\n        # START CONFIGURATION BLOCK 1\n        # END CONFIGURATION BLOCK 1\n  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write      # Grants permission to push changes to the repository\n      issues: write        # Grants permission to create or update issues\n      pull-requests: write # Grants permission to create or update pull requests\n    needs: check-for-updates\n    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}\n    strategy: # Runs for each update discovered by the `check-for-updates` job.\n      max-parallel: 1 # Ensures that the PRs/issues are created in order.\n      matrix:\n        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}\n    steps:\n      - name: Run the action\n        id: update-the-repo\n        uses: leanprover-community/mathlib-update-action/do-update@v1\n        with:\n          tag: ${{ matrix.tag }}\n          # START CONFIGURATION BLOCK 2\n          on_update_succeeds: pr # Create a pull request if the update succeeds\n          on_update_fails: issue # Create an issue if the update fails\n          # END CONFIGURATION BLOCK 2\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 428, .m_capacity = 428, .m_length = 427, .m_data = "name: Create Release\n\non:\n  push:\n    branches:\n      - 'main'\n      - 'master'\n    paths:\n      - 'lean-toolchain'\n\njobs:\n  lean-release-tag:\n    name: Add Lean release tag\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n    - name: lean-release-tag action\n      uses: leanprover-community/lean-release-tag@v1\n      with:\n        do-release: true\n        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.InitTemplate.std"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__0 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__1 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__1_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.InitTemplate.exe"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__2 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__3 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__3_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.InitTemplate.lib"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__4 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__5 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__5_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.InitTemplate.mathLax"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__6 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__7 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__7_value;
static const lean_string_object l_Lake_instReprInitTemplate_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.InitTemplate.math"};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__8 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprInitTemplate_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInitTemplate_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprInitTemplate_repr___closed__9 = (const lean_object*)&l_Lake_instReprInitTemplate_repr___closed__9_value;
static lean_once_cell_t l_Lake_instReprInitTemplate_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__10;
static lean_once_cell_t l_Lake_instReprInitTemplate_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__11;
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprInitTemplate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprInitTemplate_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprInitTemplate___closed__0 = (const lean_object*)&l_Lake_instReprInitTemplate___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprInitTemplate = (const lean_object*)&l_Lake_instReprInitTemplate___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedInitTemplate;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "std"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__0_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__1_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__2_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "math-lax"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__3_value;
static const lean_string_object l_Lake_InitTemplate_ofString_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "math"};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__4 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__4_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__5 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__5_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__6 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__6_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__7 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__7_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__8 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__8_value;
static const lean_ctor_object l_Lake_InitTemplate_ofString_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_InitTemplate_ofString_x3f___closed__9 = (const lean_object*)&l_Lake_InitTemplate_ofString_x3f___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lake.CLI.Init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "_private.Lake.CLI.Init.0.Lake.escapeName!"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "creating lean-action CI workflow"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".github"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "workflows"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_action_ci.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "created lean-action CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "update.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created Mathlib update CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "create-release.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created create-release CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "create-release CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Mathlib update CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "lean-action CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "creating a new math package with a non-release Lean toolchain; Mathlib may not work properly"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 117, .m_capacity = 117, .m_length = 116, .m_data = "could not create a `lean-toolchain` file for the new package; no known toolchain name for the current Elan/Lean/Lake"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ".gitignore"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5_value;
static const lean_array_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to initialize git repository"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Basic.lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "package already initialized"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "illegal package name '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "reserved package name"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_init___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "illegal package name: could not derive one from '"};
static const lean_object* l_Lake_init___closed__0 = (const lean_object*)&l_Lake_init___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = l_Lake_defaultLakeDir;
v___x_7_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0));
v___x_8_ = lean_string_append(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_11_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1, &l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1);
v___x_12_ = lean_string_append(v___x_11_, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3, &l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object* v_libName_19_, lean_object* v_libRoot_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_21_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0));
v___x_22_ = lean_string_append(v___x_21_, v_libName_19_);
v___x_23_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1));
v___x_24_ = lean_string_append(v___x_22_, v___x_23_);
v___x_25_ = 1;
v___x_26_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_libRoot_20_, v___x_25_);
v___x_27_ = lean_string_append(v___x_24_, v___x_26_);
lean_dec_ref(v___x_26_);
v___x_28_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2));
v___x_29_ = lean_string_append(v___x_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object* v_libName_30_, lean_object* v_libRoot_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v_libName_30_, v_libRoot_31_);
lean_dec_ref(v_libName_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object* v_libRoot_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0));
v___x_36_ = 1;
v___x_37_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_libRoot_34_, v___x_36_);
v___x_38_ = lean_string_append(v___x_35_, v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2));
v___x_40_ = lean_string_append(v___x_38_, v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0(void){
_start:
{
uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = 1;
v___x_42_ = ((lean_object*)(l_Lake_defaultExeRoot));
v___x_43_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1));
v___x_46_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0, &l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once, _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0);
v___x_47_ = lean_string_append(v___x_46_, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2, &l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object* v_libRoot_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_51_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0));
v___x_52_ = 1;
v___x_53_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_libRoot_50_, v___x_52_);
v___x_54_ = lean_string_append(v___x_51_, v___x_53_);
lean_dec_ref(v___x_53_);
v___x_55_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0));
v___x_56_ = lean_string_append(v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object* v_pkgName_63_, lean_object* v_libRoot_64_, lean_object* v_exeName_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_66_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_67_ = l_String_quote(v_pkgName_63_);
v___x_68_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
v___x_69_ = l_Std_Format_defWidth;
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l_Std_Format_pretty(v___x_68_, v___x_69_, v___x_70_, v___x_70_);
v___x_72_ = lean_string_append(v___x_66_, v___x_71_);
lean_dec_ref(v___x_71_);
v___x_73_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1));
v___x_74_ = lean_string_append(v___x_72_, v___x_73_);
v___x_75_ = lean_string_append(v___x_74_, v_libRoot_64_);
v___x_76_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2));
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
v___x_78_ = l_String_quote(v_exeName_65_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = l_Std_Format_pretty(v___x_79_, v___x_69_, v___x_70_, v___x_70_);
v___x_81_ = lean_string_append(v___x_77_, v___x_80_);
lean_dec_ref(v___x_80_);
v___x_82_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3));
v___x_83_ = lean_string_append(v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object* v_pkgName_84_, lean_object* v_libRoot_85_, lean_object* v_exeName_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgName_84_, v_libRoot_85_, v_exeName_86_);
lean_dec_ref(v_libRoot_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object* v_pkgName_93_, lean_object* v_libRoot_94_, lean_object* v_exeName_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_96_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_97_ = l_String_quote(v_pkgName_93_);
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = l_Std_Format_defWidth;
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = l_Std_Format_pretty(v___x_98_, v___x_99_, v___x_100_, v___x_100_);
v___x_102_ = lean_string_append(v___x_96_, v___x_101_);
lean_dec_ref(v___x_101_);
v___x_103_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
v___x_104_ = lean_string_append(v___x_102_, v___x_103_);
v___x_105_ = l_String_quote(v_exeName_95_);
v___x_106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___x_107_ = l_Std_Format_pretty(v___x_106_, v___x_99_, v___x_100_, v___x_100_);
v___x_108_ = lean_string_append(v___x_104_, v___x_107_);
v___x_109_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2));
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
v___x_111_ = l_String_quote(v_libRoot_94_);
v___x_112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
v___x_113_ = l_Std_Format_pretty(v___x_112_, v___x_99_, v___x_100_, v___x_100_);
v___x_114_ = lean_string_append(v___x_110_, v___x_113_);
lean_dec_ref(v___x_113_);
v___x_115_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3));
v___x_116_ = lean_string_append(v___x_114_, v___x_115_);
v___x_117_ = lean_string_append(v___x_116_, v___x_107_);
lean_dec_ref(v___x_107_);
v___x_118_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object* v_pkgName_121_, lean_object* v_exeName_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_123_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_124_ = l_String_quote(v_pkgName_121_);
v___x_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___x_126_ = l_Std_Format_defWidth;
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Std_Format_pretty(v___x_125_, v___x_126_, v___x_127_, v___x_127_);
v___x_129_ = lean_string_append(v___x_123_, v___x_128_);
lean_dec_ref(v___x_128_);
v___x_130_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0));
v___x_131_ = lean_string_append(v___x_129_, v___x_130_);
v___x_132_ = l_String_quote(v_exeName_122_);
v___x_133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
v___x_134_ = l_Std_Format_pretty(v___x_133_, v___x_126_, v___x_127_, v___x_127_);
v___x_135_ = lean_string_append(v___x_131_, v___x_134_);
lean_dec_ref(v___x_134_);
v___x_136_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3));
v___x_137_ = lean_string_append(v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object* v_pkgName_139_, lean_object* v_exeName_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_141_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_142_ = l_String_quote(v_pkgName_139_);
v___x_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = l_Std_Format_defWidth;
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = l_Std_Format_pretty(v___x_143_, v___x_144_, v___x_145_, v___x_145_);
v___x_147_ = lean_string_append(v___x_141_, v___x_146_);
lean_dec_ref(v___x_146_);
v___x_148_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
v___x_150_ = l_String_quote(v_exeName_140_);
v___x_151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = l_Std_Format_pretty(v___x_151_, v___x_144_, v___x_145_, v___x_145_);
v___x_153_ = lean_string_append(v___x_149_, v___x_152_);
v___x_154_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0));
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
v___x_156_ = lean_string_append(v___x_155_, v___x_152_);
lean_dec_ref(v___x_152_);
v___x_157_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object* v_pkgName_161_, lean_object* v_libRoot_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_163_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_164_ = l_String_quote(v_pkgName_161_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Std_Format_defWidth;
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_Std_Format_pretty(v___x_165_, v___x_166_, v___x_167_, v___x_167_);
v___x_169_ = lean_string_append(v___x_163_, v___x_168_);
lean_dec_ref(v___x_168_);
v___x_170_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0));
v___x_171_ = lean_string_append(v___x_169_, v___x_170_);
v___x_172_ = lean_string_append(v___x_171_, v_libRoot_162_);
v___x_173_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1));
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object* v_pkgName_175_, lean_object* v_libRoot_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgName_175_, v_libRoot_176_);
lean_dec_ref(v_libRoot_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object* v_pkgName_178_, lean_object* v_libRoot_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_180_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_181_ = l_String_quote(v_pkgName_178_);
v___x_182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
v___x_183_ = l_Std_Format_defWidth;
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Std_Format_pretty(v___x_182_, v___x_183_, v___x_184_, v___x_184_);
v___x_186_ = lean_string_append(v___x_180_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1));
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
v___x_189_ = l_String_quote(v_libRoot_179_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = l_Std_Format_pretty(v___x_190_, v___x_183_, v___x_184_, v___x_184_);
v___x_192_ = lean_string_append(v___x_188_, v___x_191_);
v___x_193_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = lean_string_append(v___x_194_, v___x_191_);
lean_dec_ref(v___x_191_);
v___x_196_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_197_ = lean_string_append(v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object* v_pkgName_201_, lean_object* v_libRoot_202_, lean_object* v_rev_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_204_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_205_ = l_String_quote(v_pkgName_201_);
v___x_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = l_Std_Format_defWidth;
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_Std_Format_pretty(v___x_206_, v___x_207_, v___x_208_, v___x_208_);
v___x_210_ = lean_string_append(v___x_204_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0));
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
v___x_213_ = l_String_quote(v_rev_203_);
v___x_214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = l_Std_Format_pretty(v___x_214_, v___x_207_, v___x_208_, v___x_208_);
v___x_216_ = lean_string_append(v___x_212_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1));
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
v___x_219_ = lean_string_append(v___x_218_, v_libRoot_202_);
v___x_220_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2));
v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object* v_pkgName_222_, lean_object* v_libRoot_223_, lean_object* v_rev_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgName_222_, v_libRoot_223_, v_rev_224_);
lean_dec_ref(v_libRoot_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object* v_pkgName_229_, lean_object* v_libRoot_230_, lean_object* v_rev_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_232_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_233_ = l_String_quote(v_pkgName_229_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = l_Std_Format_defWidth;
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = l_Std_Format_pretty(v___x_234_, v___x_235_, v___x_236_, v___x_236_);
v___x_238_ = lean_string_append(v___x_232_, v___x_237_);
lean_dec_ref(v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0));
v___x_240_ = lean_string_append(v___x_238_, v___x_239_);
v___x_241_ = l_String_quote(v_libRoot_230_);
v___x_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = l_Std_Format_pretty(v___x_242_, v___x_235_, v___x_236_, v___x_236_);
v___x_244_ = lean_string_append(v___x_240_, v___x_243_);
v___x_245_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = l_String_quote(v_rev_231_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = l_Std_Format_pretty(v___x_248_, v___x_235_, v___x_236_, v___x_236_);
v___x_250_ = lean_string_append(v___x_246_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2));
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
v___x_253_ = lean_string_append(v___x_252_, v___x_243_);
lean_dec_ref(v___x_243_);
v___x_254_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object* v_pkgName_257_, lean_object* v_libRoot_258_, lean_object* v_rev_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_260_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0));
v___x_261_ = l_String_quote(v_pkgName_257_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = l_Std_Format_defWidth;
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = l_Std_Format_pretty(v___x_262_, v___x_263_, v___x_264_, v___x_264_);
v___x_266_ = lean_string_append(v___x_260_, v___x_265_);
lean_dec_ref(v___x_265_);
v___x_267_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0));
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
v___x_269_ = l_String_quote(v_rev_259_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Std_Format_pretty(v___x_270_, v___x_263_, v___x_264_, v___x_264_);
v___x_272_ = lean_string_append(v___x_268_, v___x_271_);
lean_dec_ref(v___x_271_);
v___x_273_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1));
v___x_274_ = lean_string_append(v___x_272_, v___x_273_);
v___x_275_ = lean_string_append(v___x_274_, v_libRoot_258_);
v___x_276_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object* v_pkgName_278_, lean_object* v_libRoot_279_, lean_object* v_rev_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgName_278_, v_libRoot_279_, v_rev_280_);
lean_dec_ref(v_libRoot_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object* v_pkgName_283_, lean_object* v_libRoot_284_, lean_object* v_rev_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_286_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0));
v___x_287_ = l_String_quote(v_pkgName_283_);
v___x_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = l_Std_Format_defWidth;
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Std_Format_pretty(v___x_288_, v___x_289_, v___x_290_, v___x_290_);
v___x_292_ = lean_string_append(v___x_286_, v___x_291_);
lean_dec_ref(v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0));
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
v___x_295_ = l_String_quote(v_libRoot_284_);
v___x_296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___x_297_ = l_Std_Format_pretty(v___x_296_, v___x_289_, v___x_290_, v___x_290_);
v___x_298_ = lean_string_append(v___x_294_, v___x_297_);
v___x_299_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0));
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
v___x_301_ = l_String_quote(v_rev_285_);
v___x_302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = l_Std_Format_pretty(v___x_302_, v___x_289_, v___x_290_, v___x_290_);
v___x_304_ = lean_string_append(v___x_300_, v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2));
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
v___x_307_ = lean_string_append(v___x_306_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_308_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object* v_pkgName_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0));
v___x_313_ = lean_string_append(v___x_312_, v_pkgName_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object* v_pkgName_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v_pkgName_314_);
lean_dec_ref(v_pkgName_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object* v_pkgName_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0));
v___x_319_ = lean_string_append(v___x_318_, v_pkgName_317_);
v___x_320_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0));
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object* v_pkgName_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v_pkgName_322_);
lean_dec_ref(v_pkgName_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl(uint8_t v_x_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(v_x_332_);
v___x_334_ = lean_obj_tag_nat(v___x_333_);
lean_dec(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___impl___boxed(lean_object* v_x_335_){
_start:
{
uint8_t v_x_4__boxed_336_; lean_object* v_res_337_; 
v_x_4__boxed_336_ = lean_unbox(v_x_335_);
v_res_337_ = l_Lake_InitTemplate_ctorIdx___impl(v_x_4__boxed_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* v_k_338_){
_start:
{
lean_inc(v_k_338_);
return v_k_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* v_k_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lake_InitTemplate_ctorElim___redArg(v_k_339_);
lean_dec(v_k_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* v_motive_341_, lean_object* v_ctorIdx_342_, uint8_t v_t_343_, lean_object* v_h_344_, lean_object* v_k_345_){
_start:
{
lean_inc(v_k_345_);
return v_k_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* v_motive_346_, lean_object* v_ctorIdx_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_k_350_){
_start:
{
uint8_t v_t_boxed_351_; lean_object* v_res_352_; 
v_t_boxed_351_ = lean_unbox(v_t_348_);
v_res_352_ = l_Lake_InitTemplate_ctorElim(v_motive_346_, v_ctorIdx_347_, v_t_boxed_351_, v_h_349_, v_k_350_);
lean_dec(v_k_350_);
lean_dec(v_ctorIdx_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* v_std_353_){
_start:
{
lean_inc(v_std_353_);
return v_std_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* v_std_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_InitTemplate_std_elim___redArg(v_std_354_);
lean_dec(v_std_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* v_motive_356_, uint8_t v_t_357_, lean_object* v_h_358_, lean_object* v_std_359_){
_start:
{
lean_inc(v_std_359_);
return v_std_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_std_363_){
_start:
{
uint8_t v_t_boxed_364_; lean_object* v_res_365_; 
v_t_boxed_364_ = lean_unbox(v_t_361_);
v_res_365_ = l_Lake_InitTemplate_std_elim(v_motive_360_, v_t_boxed_364_, v_h_362_, v_std_363_);
lean_dec(v_std_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* v_exe_366_){
_start:
{
lean_inc(v_exe_366_);
return v_exe_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* v_exe_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lake_InitTemplate_exe_elim___redArg(v_exe_367_);
lean_dec(v_exe_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* v_motive_369_, uint8_t v_t_370_, lean_object* v_h_371_, lean_object* v_exe_372_){
_start:
{
lean_inc(v_exe_372_);
return v_exe_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* v_motive_373_, lean_object* v_t_374_, lean_object* v_h_375_, lean_object* v_exe_376_){
_start:
{
uint8_t v_t_boxed_377_; lean_object* v_res_378_; 
v_t_boxed_377_ = lean_unbox(v_t_374_);
v_res_378_ = l_Lake_InitTemplate_exe_elim(v_motive_373_, v_t_boxed_377_, v_h_375_, v_exe_376_);
lean_dec(v_exe_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* v_lib_379_){
_start:
{
lean_inc(v_lib_379_);
return v_lib_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* v_lib_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lake_InitTemplate_lib_elim___redArg(v_lib_380_);
lean_dec(v_lib_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* v_motive_382_, uint8_t v_t_383_, lean_object* v_h_384_, lean_object* v_lib_385_){
_start:
{
lean_inc(v_lib_385_);
return v_lib_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_lib_389_){
_start:
{
uint8_t v_t_boxed_390_; lean_object* v_res_391_; 
v_t_boxed_390_ = lean_unbox(v_t_387_);
v_res_391_ = l_Lake_InitTemplate_lib_elim(v_motive_386_, v_t_boxed_390_, v_h_388_, v_lib_389_);
lean_dec(v_lib_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* v_mathLax_392_){
_start:
{
lean_inc(v_mathLax_392_);
return v_mathLax_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* v_mathLax_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lake_InitTemplate_mathLax_elim___redArg(v_mathLax_393_);
lean_dec(v_mathLax_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* v_motive_395_, uint8_t v_t_396_, lean_object* v_h_397_, lean_object* v_mathLax_398_){
_start:
{
lean_inc(v_mathLax_398_);
return v_mathLax_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_mathLax_402_){
_start:
{
uint8_t v_t_boxed_403_; lean_object* v_res_404_; 
v_t_boxed_403_ = lean_unbox(v_t_400_);
v_res_404_ = l_Lake_InitTemplate_mathLax_elim(v_motive_399_, v_t_boxed_403_, v_h_401_, v_mathLax_402_);
lean_dec(v_mathLax_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* v_math_405_){
_start:
{
lean_inc(v_math_405_);
return v_math_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* v_math_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lake_InitTemplate_math_elim___redArg(v_math_406_);
lean_dec(v_math_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* v_motive_408_, uint8_t v_t_409_, lean_object* v_h_410_, lean_object* v_math_411_){
_start:
{
lean_inc(v_math_411_);
return v_math_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_math_415_){
_start:
{
uint8_t v_t_boxed_416_; lean_object* v_res_417_; 
v_t_boxed_416_ = lean_unbox(v_t_413_);
v_res_417_ = l_Lake_InitTemplate_math_elim(v_motive_412_, v_t_boxed_416_, v_h_414_, v_math_415_);
lean_dec(v_math_415_);
return v_res_417_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(2u);
v___x_434_ = lean_nat_to_int(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_to_int(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t v_x_437_, lean_object* v_prec_438_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_447_; lean_object* v___y_454_; lean_object* v___y_461_; lean_object* v___y_468_; 
switch(v_x_437_)
{
case 0:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1024u);
v___x_475_ = lean_nat_dec_le(v___x_474_, v_prec_438_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_440_ = v___x_476_;
goto v___jp_439_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_440_ = v___x_477_;
goto v___jp_439_;
}
}
case 1:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(1024u);
v___x_479_ = lean_nat_dec_le(v___x_478_, v_prec_438_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_447_ = v___x_480_;
goto v___jp_446_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_447_ = v___x_481_;
goto v___jp_446_;
}
}
case 2:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1024u);
v___x_483_ = lean_nat_dec_le(v___x_482_, v_prec_438_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_454_ = v___x_484_;
goto v___jp_453_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_454_ = v___x_485_;
goto v___jp_453_;
}
}
case 3:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1024u);
v___x_487_ = lean_nat_dec_le(v___x_486_, v_prec_438_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_461_ = v___x_488_;
goto v___jp_460_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_461_ = v___x_489_;
goto v___jp_460_;
}
}
default: 
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(1024u);
v___x_491_ = lean_nat_dec_le(v___x_490_, v_prec_438_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_468_ = v___x_492_;
goto v___jp_467_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_468_ = v___x_493_;
goto v___jp_467_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__1));
lean_inc(v___y_440_);
v___x_442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = 0;
v___x_444_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*1, v___x_443_);
v___x_445_ = l_Repr_addAppParen(v___x_444_, v_prec_438_);
return v___x_445_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__3));
lean_inc(v___y_447_);
v___x_449_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_449_, 0, v___y_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = 0;
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = l_Repr_addAppParen(v___x_451_, v_prec_438_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__5));
lean_inc(v___y_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_438_);
return v___x_459_;
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__7));
lean_inc(v___y_461_);
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = 0;
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_464_);
v___x_466_ = l_Repr_addAppParen(v___x_465_, v_prec_438_);
return v___x_466_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__9));
lean_inc(v___y_468_);
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___y_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = 0;
v___x_472_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*1, v___x_471_);
v___x_473_ = l_Repr_addAppParen(v___x_472_, v_prec_438_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* v_x_494_, lean_object* v_prec_495_){
_start:
{
uint8_t v_x_279__boxed_496_; lean_object* v_res_497_; 
v_x_279__boxed_496_ = lean_unbox(v_x_494_);
v_res_497_ = l_Lake_instReprInitTemplate_repr(v_x_279__boxed_496_, v_prec_495_);
lean_dec(v_prec_495_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object* v_n_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_dec_le(v_n_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(2u);
v___x_504_ = lean_nat_dec_le(v_n_500_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = lean_nat_dec_le(v_n_500_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = 4;
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = 3;
return v___x_508_;
}
}
else
{
uint8_t v___x_509_; 
v___x_509_ = 2;
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_nat_dec_le(v_n_500_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = 1;
return v___x_512_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* v_n_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Lake_InitTemplate_ofNat(v_n_514_);
lean_dec(v_n_514_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t v_x_517_, uint8_t v_y_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_519_ = lean_box(v_x_517_);
v___x_520_ = lean_obj_tag_nat(v___x_519_);
lean_dec(v___x_519_);
v___x_521_ = lean_box(v_y_518_);
v___x_522_ = lean_obj_tag_nat(v___x_521_);
lean_dec(v___x_521_);
v___x_523_ = lean_nat_dec_eq(v___x_520_, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* v_x_524_, lean_object* v_y_525_){
_start:
{
uint8_t v_x_23__boxed_526_; uint8_t v_y_24__boxed_527_; uint8_t v_res_528_; lean_object* v_r_529_; 
v_x_23__boxed_526_ = lean_unbox(v_x_524_);
v_y_24__boxed_527_ = lean_unbox(v_y_525_);
v_res_528_ = l_Lake_instDecidableEqInitTemplate(v_x_23__boxed_526_, v_y_24__boxed_527_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate(void){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__0));
v___x_553_ = lean_string_dec_eq(v_x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__1));
v___x_555_ = lean_string_dec_eq(v_x_551_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__2));
v___x_557_ = lean_string_dec_eq(v_x_551_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__3));
v___x_559_ = lean_string_dec_eq(v_x_551_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__4));
v___x_561_ = lean_string_dec_eq(v_x_551_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__5));
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__6));
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__7));
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__8));
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__9));
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lake_InitTemplate_ofString_x3f(v_x_568_);
lean_dec_ref(v_x_568_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1(void){
_start:
{
uint32_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_idBeginEscape;
v___x_572_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_573_ = lean_string_push(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2(void){
_start:
{
uint32_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l_Lean_idEndEscape;
v___x_575_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_576_ = lean_string_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* v_id_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
v___x_579_ = lean_string_append(v___x_578_, v_id_577_);
v___x_580_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* v_id_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_id_582_);
lean_dec_ref(v_id_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* v_msg_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_586_ = lean_panic_fn_borrowed(v___x_585_, v_msg_584_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_590_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_591_ = lean_unsigned_to_nat(23u);
v___x_592_ = lean_unsigned_to_nat(350u);
v___x_593_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_594_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_595_ = l_mkPanicMessageWithDecl(v___x_594_, v___x_593_, v___x_592_, v___x_591_, v___x_590_);
return v___x_595_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_598_ = lean_unsigned_to_nat(23u);
v___x_599_ = lean_unsigned_to_nat(353u);
v___x_600_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_601_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_602_ = l_mkPanicMessageWithDecl(v___x_601_, v___x_600_, v___x_599_, v___x_598_, v___x_597_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* v_x_603_){
_start:
{
switch(lean_obj_tag(v_x_603_))
{
case 0:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
v___x_605_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_604_);
return v___x_605_;
}
case 1:
{
lean_object* v_pre_606_; 
v_pre_606_ = lean_ctor_get(v_x_603_, 0);
if (lean_obj_tag(v_pre_606_) == 0)
{
lean_object* v_str_607_; lean_object* v___x_608_; 
v_str_607_ = lean_ctor_get(v_x_603_, 1);
v___x_608_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_607_);
return v___x_608_;
}
else
{
lean_object* v_str_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_str_609_ = lean_ctor_get(v_x_603_, 1);
v___x_610_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_pre_606_);
v___x_611_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_609_);
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
lean_dec_ref(v___x_613_);
return v___x_614_;
}
}
default: 
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
v___x_616_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_615_);
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_x_617_);
lean_dec(v_x_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* v_s_619_, lean_object* v_p_620_){
_start:
{
uint32_t v___y_622_; lean_object* v___x_627_; uint8_t v_decide_628_; 
v___x_627_ = lean_string_utf8_byte_size(v_s_619_);
v_decide_628_ = lean_nat_dec_eq(v_p_620_, v___x_627_);
if (v_decide_628_ == 0)
{
uint32_t v___x_629_; uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_string_utf8_get_fast(v_s_619_, v_p_620_);
v___x_630_ = 46;
v___x_631_ = lean_uint32_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
v___y_622_ = v___x_629_;
goto v___jp_621_;
}
else
{
uint32_t v___x_632_; 
v___x_632_ = 45;
v___y_622_ = v___x_632_;
goto v___jp_621_;
}
}
else
{
lean_dec(v_p_620_);
return v_s_619_;
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_inc(v_p_620_);
v___x_623_ = lean_string_utf8_set(v_s_619_, v_p_620_, v___y_622_);
v___x_624_ = l_Char_utf8Size(v___y_622_);
v___x_625_ = lean_nat_add(v_p_620_, v___x_624_);
lean_dec(v___x_624_);
lean_dec(v_p_620_);
v_s_619_ = v___x_623_;
v_p_620_ = v___x_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* v_name_633_){
_start:
{
uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = 0;
v___x_635_ = l_Lean_Name_toString(v_name_633_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(v___x_635_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* v_s_638_, lean_object* v_p_639_){
_start:
{
uint32_t v___y_641_; lean_object* v___x_646_; uint8_t v_decide_647_; 
v___x_646_ = lean_string_utf8_byte_size(v_s_638_);
v_decide_647_ = lean_nat_dec_eq(v_p_639_, v___x_646_);
if (v_decide_647_ == 0)
{
uint32_t v___x_648_; uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_648_ = lean_string_utf8_get_fast(v_s_638_, v_p_639_);
v___x_649_ = 65;
v___x_650_ = lean_uint32_dec_le(v___x_649_, v___x_648_);
if (v___x_650_ == 0)
{
v___y_641_ = v___x_648_;
goto v___jp_640_;
}
else
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 90;
v___x_652_ = lean_uint32_dec_le(v___x_648_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_641_ = v___x_648_;
goto v___jp_640_;
}
else
{
uint32_t v___x_653_; uint32_t v___x_654_; 
v___x_653_ = 32;
v___x_654_ = lean_uint32_add(v___x_648_, v___x_653_);
v___y_641_ = v___x_654_;
goto v___jp_640_;
}
}
}
else
{
lean_dec(v_p_639_);
return v_s_638_;
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_inc(v_p_639_);
v___x_642_ = lean_string_utf8_set(v_s_638_, v_p_639_, v___y_641_);
v___x_643_ = l_Char_utf8Size(v___y_641_);
v___x_644_ = lean_nat_add(v_p_639_, v___x_643_);
lean_dec(v___x_643_);
lean_dec(v_p_639_);
v_s_638_ = v___x_642_;
v_p_639_ = v___x_644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t v_tmp_657_, uint8_t v_lang_658_, lean_object* v_pkgName_659_, lean_object* v_root_660_, lean_object* v_leanVer_x3f_661_){
_start:
{
lean_object* v_pkgNameStr_662_; lean_object* v___y_664_; 
v_pkgNameStr_662_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_659_);
if (lean_obj_tag(v_leanVer_x3f_661_) == 0)
{
lean_object* v___x_695_; 
v___x_695_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___y_664_ = v___x_695_;
goto v___jp_663_;
}
else
{
lean_object* v_val_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_val_696_ = lean_ctor_get(v_leanVer_x3f_661_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_leanVer_x3f_661_, 1);
v___x_697_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
v___x_698_ = l_Lake_StdVer_toString(v_val_696_);
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
lean_dec_ref(v___x_698_);
v___y_664_ = v___x_699_;
goto v___jp_663_;
}
v___jp_663_:
{
switch(v_tmp_657_)
{
case 0:
{
lean_dec_ref(v___y_664_);
if (v_lang_658_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_660_);
lean_dec(v_root_660_);
v___x_666_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_662_);
v___x_667_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_662_, v___x_666_);
v___x_668_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgNameStr_662_, v___x_665_, v___x_667_);
lean_dec_ref(v___x_665_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_669_ = 1;
v___x_670_ = l_Lean_Name_toString(v_root_660_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_662_);
v___x_672_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_662_, v___x_671_);
v___x_673_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(v_pkgNameStr_662_, v___x_670_, v___x_672_);
return v___x_673_;
}
}
case 1:
{
lean_dec_ref(v___y_664_);
lean_dec(v_root_660_);
if (v_lang_658_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_662_);
v___x_675_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_662_, v___x_674_);
v___x_676_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(v_pkgNameStr_662_, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_662_);
v___x_678_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_662_, v___x_677_);
v___x_679_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(v_pkgNameStr_662_, v___x_678_);
return v___x_679_;
}
}
case 2:
{
lean_dec_ref(v___y_664_);
if (v_lang_658_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_660_);
lean_dec(v_root_660_);
v___x_681_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgNameStr_662_, v___x_680_);
lean_dec_ref(v___x_680_);
return v___x_681_;
}
else
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = 1;
v___x_683_ = l_Lean_Name_toString(v_root_660_, v___x_682_);
v___x_684_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(v_pkgNameStr_662_, v___x_683_);
return v___x_684_;
}
}
case 3:
{
if (v_lang_658_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_660_);
lean_dec(v_root_660_);
v___x_686_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgNameStr_662_, v___x_685_, v___y_664_);
lean_dec_ref(v___x_685_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = 1;
v___x_688_ = l_Lean_Name_toString(v_root_660_, v___x_687_);
v___x_689_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(v_pkgNameStr_662_, v___x_688_, v___y_664_);
return v___x_689_;
}
}
default: 
{
if (v_lang_658_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_660_);
lean_dec(v_root_660_);
v___x_691_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgNameStr_662_, v___x_690_, v___y_664_);
lean_dec_ref(v___x_690_);
return v___x_691_;
}
else
{
uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = 1;
v___x_693_ = l_Lean_Name_toString(v_root_660_, v___x_692_);
v___x_694_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(v_pkgNameStr_662_, v___x_693_, v___y_664_);
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* v_tmp_700_, lean_object* v_lang_701_, lean_object* v_pkgName_702_, lean_object* v_root_703_, lean_object* v_leanVer_x3f_704_){
_start:
{
uint8_t v_tmp_boxed_705_; uint8_t v_lang_boxed_706_; lean_object* v_res_707_; 
v_tmp_boxed_705_ = lean_unbox(v_tmp_700_);
v_lang_boxed_706_ = lean_unbox(v_lang_701_);
v_res_707_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_boxed_705_, v_lang_boxed_706_, v_pkgName_702_, v_root_703_, v_leanVer_x3f_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* v_dir_733_, uint8_t v_tmp_734_, lean_object* v_a_735_){
_start:
{
uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_737_ = 0;
v___x_738_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
v___x_739_ = lean_array_push(v_a_735_, v___x_738_);
v___x_740_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
v___x_741_ = l_Lake_joinRelative(v_dir_733_, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
v___x_743_ = l_Lake_joinRelative(v___x_741_, v___x_742_);
lean_inc_ref(v___x_743_);
v___x_744_ = l_IO_FS_createDirAll(v___x_743_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___y_748_; uint8_t v___x_805_; 
lean_dec_ref_known(v___x_744_, 1);
v___x_745_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(v___x_743_);
v___x_746_ = l_Lake_joinRelative(v___x_743_, v___x_745_);
v___x_805_ = l_System_FilePath_pathExists(v___x_746_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_806_ = lean_box(v_tmp_734_);
v___x_807_ = lean_obj_tag_nat(v___x_806_);
lean_dec(v___x_806_);
v___x_808_ = lean_unsigned_to_nat(4u);
v___x_809_ = lean_nat_dec_eq(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
v___x_811_ = l_IO_FS_writeFile(v___x_746_, v___x_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_dec_ref_known(v___x_811_, 1);
v___y_748_ = v___x_739_;
goto v___jp_747_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_743_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = lean_io_error_to_string(v_a_812_);
v___x_814_ = 3;
v___x_815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*1, v___x_814_);
v___x_816_ = lean_array_get_size(v___x_739_);
v___x_817_ = lean_array_push(v___x_739_, v___x_815_);
v___x_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
return v___x_818_;
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
v___x_820_ = l_IO_FS_writeFile(v___x_746_, v___x_819_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref_known(v___x_820_, 1);
v___y_748_ = v___x_739_;
goto v___jp_747_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_743_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = lean_io_error_to_string(v_a_821_);
v___x_823_ = 3;
v___x_824_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*1, v___x_823_);
v___x_825_ = lean_array_get_size(v___x_739_);
v___x_826_ = lean_array_push(v___x_739_, v___x_824_);
v___x_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
return v___x_827_;
}
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_743_);
v___x_828_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
v___x_829_ = lean_array_push(v___x_739_, v___x_828_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
return v___x_831_;
}
v___jp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_749_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
v___x_750_ = lean_string_append(v___x_749_, v___x_746_);
lean_dec_ref(v___x_746_);
v___x_751_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*1, v___x_737_);
v___x_754_ = lean_array_push(v___y_748_, v___x_753_);
v___x_755_ = lean_box(v_tmp_734_);
v___x_756_ = lean_obj_tag_nat(v___x_755_);
lean_dec(v___x_755_);
v___x_757_ = lean_unsigned_to_nat(4u);
v___x_758_ = lean_nat_dec_eq(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec_ref(v___x_743_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v___x_754_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(v___x_743_);
v___x_762_ = l_Lake_joinRelative(v___x_743_, v___x_761_);
v___x_763_ = l_System_FilePath_pathExists(v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
v___x_765_ = l_IO_FS_writeFile(v___x_762_, v___x_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
lean_dec_ref_known(v___x_765_, 1);
v___x_766_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
v___x_767_ = lean_string_append(v___x_766_, v___x_762_);
lean_dec_ref(v___x_762_);
v___x_768_ = lean_string_append(v___x_767_, v___x_751_);
v___x_769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_737_);
v___x_770_ = lean_array_push(v___x_754_, v___x_769_);
v___x_771_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
v___x_772_ = l_Lake_joinRelative(v___x_743_, v___x_771_);
v___x_773_ = l_System_FilePath_pathExists(v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
v___x_775_ = l_IO_FS_writeFile(v___x_772_, v___x_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref_known(v___x_775_, 1);
v___x_776_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
v___x_777_ = lean_string_append(v___x_776_, v___x_772_);
lean_dec_ref(v___x_772_);
v___x_778_ = lean_string_append(v___x_777_, v___x_751_);
v___x_779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_737_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_array_push(v___x_770_, v___x_779_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v___x_772_);
v_a_783_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_775_, 1);
v___x_784_ = lean_io_error_to_string(v_a_783_);
v___x_785_ = 3;
v___x_786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*1, v___x_785_);
v___x_787_ = lean_array_get_size(v___x_770_);
v___x_788_ = lean_array_push(v___x_770_, v___x_786_);
v___x_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v___x_772_);
v___x_790_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
v___x_791_ = lean_array_push(v___x_770_, v___x_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
return v___x_793_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_743_);
v_a_794_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_765_, 1);
v___x_795_ = lean_io_error_to_string(v_a_794_);
v___x_796_ = 3;
v___x_797_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*1, v___x_796_);
v___x_798_ = lean_array_get_size(v___x_754_);
v___x_799_ = lean_array_push(v___x_754_, v___x_797_);
v___x_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
return v___x_800_;
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_743_);
v___x_801_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
v___x_802_ = lean_array_push(v___x_754_, v___x_801_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v___x_743_);
v_a_832_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_744_, 1);
v___x_833_ = lean_io_error_to_string(v_a_832_);
v___x_834_ = 3;
v___x_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*1, v___x_834_);
v___x_836_ = lean_array_get_size(v___x_739_);
v___x_837_ = lean_array_push(v___x_739_, v___x_835_);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* v_dir_839_, lean_object* v_tmp_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
uint8_t v_tmp_boxed_843_; lean_object* v_res_844_; 
v_tmp_boxed_843_ = lean_unbox(v_tmp_840_);
v_res_844_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_839_, v_tmp_boxed_843_, v_a_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* v_as_845_, size_t v_i_846_, size_t v_stop_847_, lean_object* v_b_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_eq(v_i_846_, v_stop_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; 
v___x_852_ = lean_array_uget_borrowed(v_as_845_, v_i_846_);
lean_inc_ref(v___y_849_);
lean_inc(v___x_852_);
v___x_853_ = lean_apply_2(v___y_849_, v___x_852_, lean_box(0));
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_846_, v___x_854_);
v_i_846_ = v___x_855_;
v_b_848_ = v___x_853_;
goto _start;
}
else
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v_b_848_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* v_as_858_, lean_object* v_i_859_, lean_object* v_stop_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
size_t v_i_boxed_864_; size_t v_stop_boxed_865_; lean_object* v_res_866_; 
v_i_boxed_864_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_stop_boxed_865_ = lean_unbox_usize(v_stop_860_);
lean_dec(v_stop_860_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_858_, v_i_boxed_864_, v_stop_boxed_865_, v_b_861_, v___y_862_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_as_858_);
return v_res_866_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_881_ = lean_array_get_size(v___x_880_);
return v___x_881_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_882_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_nat_dec_lt(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_885_; size_t v___x_886_; 
v___x_885_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_886_ = lean_usize_of_nat(v___x_885_);
return v___x_886_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_892_ = l_Lake_Git_upstreamBranch;
v___x_893_ = lean_string_dec_eq(v___x_892_, v___x_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_901_, lean_object* v_name_902_, uint8_t v_tmp_903_, uint8_t v_lang_904_, lean_object* v_env_905_, uint8_t v_offline_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___y_911_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v_a_941_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; uint8_t v_a_1061_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v_a_1118_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; uint8_t v_a_1148_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v_a_1249_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_configFile_1281_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v_fst_1316_; lean_object* v_snd_1317_; lean_object* v___y_1327_; lean_object* v___y_1328_; uint8_t v_a_1329_; lean_object* v___y_1333_; uint8_t v_a_1334_; lean_object* v___y_1359_; uint8_t v_a_1361_; lean_object* v___x_1393_; uint8_t v___x_1394_; uint8_t v___x_1395_; 
v___x_909_ = l_Lake_defaultConfigFile;
v___x_1279_ = l_Lake_ConfigLang_fileExtension(v_lang_904_);
v___x_1280_ = l_System_FilePath_addExtension(v___x_909_, v___x_1279_);
lean_dec_ref(v___x_1279_);
lean_inc_ref(v_dir_901_);
v_configFile_1281_ = l_Lake_joinRelative(v_dir_901_, v___x_1280_);
v___x_1393_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1394_ = l_System_FilePath_pathExists(v_configFile_1281_);
v___x_1395_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1395_ == 0)
{
v_a_1361_ = v___x_1394_;
goto v___jp_1360_;
}
else
{
lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1393_, v___x_1397_, v___x_1398_, v___x_1396_, v_a_907_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec_ref_known(v___x_1399_, 1);
v_a_1361_ = v___x_1394_;
goto v___jp_1360_;
}
else
{
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___x_1399_;
}
}
v___jp_910_:
{
if (v_offline_906_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_box(0);
v___x_915_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_901_);
v___x_916_ = l_Lake_joinRelative(v_dir_901_, v___x_915_);
lean_inc_ref(v___x_916_);
v___x_917_ = l_Lake_joinRelative(v___x_916_, v___x_909_);
v___x_918_ = l_Lake_defaultManifestFile;
v___x_919_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_920_ = lean_box(1);
v___x_921_ = l_Lean_Options_empty;
v___x_922_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_923_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_923_, 0, v_env_905_);
lean_ctor_set(v___x_923_, 1, v___x_912_);
lean_ctor_set(v___x_923_, 2, v_dir_901_);
lean_ctor_set(v___x_923_, 3, v___x_913_);
lean_ctor_set(v___x_923_, 4, v___x_914_);
lean_ctor_set(v___x_923_, 5, v___x_915_);
lean_ctor_set(v___x_923_, 6, v___x_916_);
lean_ctor_set(v___x_923_, 7, v___x_909_);
lean_ctor_set(v___x_923_, 8, v___x_917_);
lean_ctor_set(v___x_923_, 9, v___x_912_);
lean_ctor_set(v___x_923_, 10, v___x_918_);
lean_ctor_set(v___x_923_, 11, v___x_919_);
lean_ctor_set(v___x_923_, 12, v___x_920_);
lean_ctor_set(v___x_923_, 13, v___x_921_);
lean_ctor_set(v___x_923_, 14, v___x_922_);
lean_ctor_set(v___x_923_, 15, v___x_922_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*16, v_offline_906_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*16 + 1, v_offline_906_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*16 + 2, v_offline_906_);
v___x_924_ = l_Lean_NameSet_empty;
v___x_925_ = l_Lake_updateManifest(v___x_923_, v___x_924_, v___y_911_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
v___jp_928_:
{
if (lean_obj_tag(v___y_930_) == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_929_);
v___x_932_ = lean_apply_2(v___y_929_, v___x_931_, lean_box(0));
v___y_911_ = v___y_929_;
goto v___jp_910_;
}
else
{
lean_dec_ref_known(v___y_930_, 1);
v___y_911_ = v___y_929_;
goto v___jp_910_;
}
}
v___jp_933_:
{
switch(v_tmp_903_)
{
case 3:
{
v___y_929_ = v___y_935_;
v___y_930_ = v___y_934_;
goto v___jp_928_;
}
case 4:
{
v___y_929_ = v___y_935_;
v___y_930_ = v___y_934_;
goto v___jp_928_;
}
default: 
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v___y_934_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
v___x_936_ = lean_box(0);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
v___jp_938_:
{
if (v_a_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_939_);
v___x_943_ = lean_apply_2(v___y_939_, v___x_942_, lean_box(0));
v___y_934_ = v___y_940_;
v___y_935_ = v___y_939_;
goto v___jp_933_;
}
else
{
v___y_934_ = v___y_940_;
v___y_935_ = v___y_939_;
goto v___jp_933_;
}
}
v___jp_944_:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; 
v___x_949_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_901_);
v___x_950_ = l_Lake_joinRelative(v_dir_901_, v___x_949_);
v___x_951_ = 4;
v___x_952_ = lean_io_prim_handle_mk(v___x_950_, v___x_951_);
lean_dec_ref(v___x_950_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_955_ = lean_io_prim_handle_put_str(v_a_953_, v___x_954_);
lean_dec(v_a_953_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
lean_dec_ref_known(v___x_955_, 1);
v___x_956_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_901_);
v___x_957_ = l_Lake_joinRelative(v_dir_901_, v___x_956_);
v___x_958_ = lean_string_utf8_byte_size(v___y_946_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_nat_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v___y_945_);
v___x_961_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_962_ = lean_string_append(v___y_946_, v___x_961_);
v___x_963_ = l_IO_FS_writeFile(v___x_957_, v___x_962_);
lean_dec_ref(v___x_962_);
lean_dec_ref(v___x_957_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_dec_ref_known(v___x_963_, 1);
v___y_934_ = v___y_947_;
v___y_935_ = v___y_948_;
goto v___jp_933_;
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_976_; 
lean_dec(v___y_947_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_976_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_976_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_968_ = lean_io_error_to_string(v_a_964_);
v___x_969_ = 3;
v___x_970_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_969_);
lean_inc_ref(v___y_948_);
v___x_971_ = lean_apply_2(v___y_948_, v___x_970_, lean_box(0));
v___x_972_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_972_);
v___x_974_ = v___x_966_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_githash_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
lean_dec_ref(v___y_946_);
v_githash_977_ = lean_ctor_get(v___y_945_, 1);
lean_inc_ref(v_githash_977_);
lean_dec_ref(v___y_945_);
v___x_978_ = lean_string_utf8_byte_size(v_githash_977_);
lean_dec_ref(v_githash_977_);
v___x_979_ = lean_nat_dec_eq(v___x_978_, v___x_959_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; uint8_t v___x_981_; uint8_t v___x_982_; 
v___x_980_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_981_ = l_System_FilePath_pathExists(v___x_957_);
lean_dec_ref(v___x_957_);
v___x_982_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_982_ == 0)
{
v___y_939_ = v___y_948_;
v___y_940_ = v___y_947_;
v_a_941_ = v___x_981_;
goto v___jp_938_;
}
else
{
lean_object* v___x_983_; size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_983_ = lean_box(0);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_980_, v___x_984_, v___x_985_, v___x_983_, v___y_948_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_dec_ref_known(v___x_986_, 1);
v___y_939_ = v___y_948_;
v___y_940_ = v___y_947_;
v_a_941_ = v___x_981_;
goto v___jp_938_;
}
else
{
lean_dec(v___y_947_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
return v___x_986_;
}
}
}
else
{
lean_dec_ref(v___x_957_);
v___y_934_ = v___y_947_;
v___y_935_ = v___y_948_;
goto v___jp_933_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
v_a_987_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_999_ == 0)
{
v___x_989_ = v___x_955_;
v_isShared_990_ = v_isSharedCheck_999_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_955_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_999_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_991_ = lean_io_error_to_string(v_a_987_);
v___x_992_ = 3;
v___x_993_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_992_);
lean_inc_ref(v___y_948_);
v___x_994_ = lean_apply_2(v___y_948_, v___x_993_, lean_box(0));
v___x_995_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_995_);
v___x_997_ = v___x_989_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
v_a_1000_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1002_ = v___x_952_;
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_952_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1004_ = lean_io_error_to_string(v_a_1000_);
v___x_1005_ = 3;
v___x_1006_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_1005_);
lean_inc_ref(v___y_948_);
v___x_1007_ = lean_apply_2(v___y_948_, v___x_1006_, lean_box(0));
v___x_1008_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1008_);
v___x_1010_ = v___x_1002_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
v___jp_1013_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1016_);
v___x_1019_ = lean_apply_2(v___y_1016_, v___x_1018_, lean_box(0));
v___y_945_ = v___y_1014_;
v___y_946_ = v___y_1015_;
v___y_947_ = v___y_1017_;
v___y_948_ = v___y_1016_;
goto v___jp_944_;
}
v___jp_1020_:
{
if (lean_obj_tag(v___y_1025_) == 0)
{
lean_dec_ref_known(v___y_1025_, 1);
v___y_945_ = v___y_1021_;
v___y_946_ = v___y_1022_;
v___y_947_ = v___y_1024_;
v___y_948_ = v___y_1023_;
goto v___jp_944_;
}
else
{
lean_dec_ref_known(v___y_1025_, 1);
v___y_1014_ = v___y_1021_;
v___y_1015_ = v___y_1022_;
v___y_1016_ = v___y_1023_;
v___y_1017_ = v___y_1024_;
goto v___jp_1013_;
}
}
v___jp_1026_:
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = l_Lake_Git_upstreamBranch;
v___x_1032_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_901_);
v___x_1035_ = l_Lake_GitRepo_checkoutBranch(v___x_1031_, v_dir_901_, v___x_1034_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 2);
v___x_1037_ = lean_array_get_size(v_a_1036_);
v___x_1038_ = lean_nat_dec_lt(v___x_1033_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec(v_a_1036_);
v___y_945_ = v___y_1027_;
v___y_946_ = v___y_1028_;
v___y_947_ = v___y_1030_;
v___y_948_ = v___y_1029_;
goto v___jp_944_;
}
else
{
lean_object* v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1037_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1036_, v___x_1040_, v___x_1041_, v___x_1039_, v___y_1029_);
lean_dec(v_a_1036_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref_known(v___x_1042_, 1);
v___y_945_ = v___y_1027_;
v___y_946_ = v___y_1028_;
v___y_947_ = v___y_1030_;
v___y_948_ = v___y_1029_;
goto v___jp_944_;
}
else
{
v___y_1021_ = v___y_1027_;
v___y_1022_ = v___y_1028_;
v___y_1023_ = v___y_1029_;
v___y_1024_ = v___y_1030_;
v___y_1025_ = v___x_1042_;
goto v___jp_1020_;
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_a_1043_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1035_, 2);
v___x_1044_ = lean_array_get_size(v_a_1043_);
v___x_1045_ = lean_nat_dec_lt(v___x_1033_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v_a_1043_);
v___y_1014_ = v___y_1027_;
v___y_1015_ = v___y_1028_;
v___y_1016_ = v___y_1029_;
v___y_1017_ = v___y_1030_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = lean_usize_of_nat(v___x_1044_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1043_, v___x_1047_, v___x_1048_, v___x_1046_, v___y_1029_);
lean_dec(v_a_1043_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_dec_ref_known(v___x_1049_, 1);
v___y_1014_ = v___y_1027_;
v___y_1015_ = v___y_1028_;
v___y_1016_ = v___y_1029_;
v___y_1017_ = v___y_1030_;
goto v___jp_1013_;
}
else
{
v___y_1021_ = v___y_1027_;
v___y_1022_ = v___y_1028_;
v___y_1023_ = v___y_1029_;
v___y_1024_ = v___y_1030_;
v___y_1025_ = v___x_1049_;
goto v___jp_1020_;
}
}
}
}
else
{
v___y_945_ = v___y_1027_;
v___y_946_ = v___y_1028_;
v___y_947_ = v___y_1030_;
v___y_948_ = v___y_1029_;
goto v___jp_944_;
}
}
v___jp_1050_:
{
if (lean_obj_tag(v___y_1055_) == 0)
{
lean_dec_ref_known(v___y_1055_, 1);
v___y_1027_ = v___y_1051_;
v___y_1028_ = v___y_1052_;
v___y_1029_ = v___y_1053_;
v___y_1030_ = v___y_1054_;
goto v___jp_1026_;
}
else
{
lean_dec_ref_known(v___y_1055_, 1);
v___y_1014_ = v___y_1051_;
v___y_1015_ = v___y_1052_;
v___y_1016_ = v___y_1053_;
v___y_1017_ = v___y_1054_;
goto v___jp_1013_;
}
}
v___jp_1056_:
{
if (v_a_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_901_);
v___x_1064_ = l_Lake_GitRepo_quietInit(v_dir_901_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 1);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 2);
v___x_1066_ = lean_array_get_size(v_a_1065_);
v___x_1067_ = lean_nat_dec_lt(v___x_1062_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec(v_a_1065_);
v___y_1027_ = v___y_1057_;
v___y_1028_ = v___y_1058_;
v___y_1029_ = v___y_1059_;
v___y_1030_ = v___y_1060_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = lean_usize_of_nat(v___x_1066_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1065_, v___x_1069_, v___x_1070_, v___x_1068_, v___y_1059_);
lean_dec(v_a_1065_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_dec_ref_known(v___x_1071_, 1);
v___y_1027_ = v___y_1057_;
v___y_1028_ = v___y_1058_;
v___y_1029_ = v___y_1059_;
v___y_1030_ = v___y_1060_;
goto v___jp_1026_;
}
else
{
v___y_1051_ = v___y_1057_;
v___y_1052_ = v___y_1058_;
v___y_1053_ = v___y_1059_;
v___y_1054_ = v___y_1060_;
v___y_1055_ = v___x_1071_;
goto v___jp_1050_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1064_, 1);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1064_, 2);
v___x_1073_ = lean_array_get_size(v_a_1072_);
v___x_1074_ = lean_nat_dec_lt(v___x_1062_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec(v_a_1072_);
v___y_1014_ = v___y_1057_;
v___y_1015_ = v___y_1058_;
v___y_1016_ = v___y_1059_;
v___y_1017_ = v___y_1060_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = lean_usize_of_nat(v___x_1073_);
v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1072_, v___x_1076_, v___x_1077_, v___x_1075_, v___y_1059_);
lean_dec(v_a_1072_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_dec_ref_known(v___x_1078_, 1);
v___y_1014_ = v___y_1057_;
v___y_1015_ = v___y_1058_;
v___y_1016_ = v___y_1059_;
v___y_1017_ = v___y_1060_;
goto v___jp_1013_;
}
else
{
v___y_1051_ = v___y_1057_;
v___y_1052_ = v___y_1058_;
v___y_1053_ = v___y_1059_;
v___y_1054_ = v___y_1060_;
v___y_1055_ = v___x_1078_;
goto v___jp_1050_;
}
}
}
}
else
{
v___y_945_ = v___y_1057_;
v___y_946_ = v___y_1058_;
v___y_947_ = v___y_1060_;
v___y_948_ = v___y_1059_;
goto v___jp_944_;
}
}
v___jp_1079_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_901_);
v___x_1085_ = l_Lake_GitRepo_insideWorkTree(v_dir_901_);
v___x_1086_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1086_ == 0)
{
v___y_1057_ = v___y_1080_;
v___y_1058_ = v___y_1081_;
v___y_1059_ = v___y_1083_;
v___y_1060_ = v___y_1082_;
v_a_1061_ = v___x_1085_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1084_, v___x_1088_, v___x_1089_, v___x_1087_, v___y_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec_ref_known(v___x_1090_, 1);
v___y_1057_ = v___y_1080_;
v___y_1058_ = v___y_1081_;
v___y_1059_ = v___y_1083_;
v___y_1060_ = v___y_1082_;
v_a_1061_ = v___x_1085_;
goto v___jp_1056_;
}
else
{
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
return v___x_1090_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_IO_FS_writeFile(v___y_1095_, v___y_1097_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___y_1095_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref_known(v___x_1098_, 1);
v___y_1080_ = v___y_1092_;
v___y_1081_ = v___y_1094_;
v___y_1082_ = v___y_1096_;
v___y_1083_ = v___y_1093_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v_env_905_);
lean_dec_ref(v_dir_901_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1103_ = lean_io_error_to_string(v_a_1099_);
v___x_1104_ = 3;
v___x_1105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*1, v___x_1104_);
lean_inc_ref(v___y_1093_);
v___x_1106_ = lean_apply_2(v___y_1093_, v___x_1105_, lean_box(0));
v___x_1107_ = lean_box(0);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1107_);
v___x_1109_ = v___x_1101_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
if (v_a_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1119_ = lean_box(v_tmp_903_);
v___x_1120_ = lean_obj_tag_nat(v___x_1119_);
lean_dec(v___x_1119_);
v___x_1121_ = lean_unsigned_to_nat(4u);
v___x_1122_ = lean_nat_dec_eq(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_902_);
v___x_1124_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1123_);
lean_dec_ref(v___x_1123_);
v___y_1092_ = v___y_1114_;
v___y_1093_ = v___y_1113_;
v___y_1094_ = v___y_1116_;
v___y_1095_ = v___y_1115_;
v___y_1096_ = v___y_1117_;
v___y_1097_ = v___x_1124_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_902_);
v___x_1126_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1125_);
lean_dec_ref(v___x_1125_);
v___y_1092_ = v___y_1114_;
v___y_1093_ = v___y_1113_;
v___y_1094_ = v___y_1116_;
v___y_1095_ = v___y_1115_;
v___y_1096_ = v___y_1117_;
v___y_1097_ = v___x_1126_;
goto v___jp_1091_;
}
}
else
{
lean_dec_ref(v___y_1115_);
lean_dec(v_name_902_);
v___y_1080_ = v___y_1114_;
v___y_1081_ = v___y_1116_;
v___y_1082_ = v___y_1117_;
v___y_1083_ = v___y_1113_;
goto v___jp_1079_;
}
}
v___jp_1127_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1132_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_901_);
v___x_1133_ = l_Lake_joinRelative(v_dir_901_, v___x_1132_);
v___x_1134_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1135_ = l_System_FilePath_pathExists(v___x_1133_);
v___x_1136_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1136_ == 0)
{
v___y_1113_ = v___y_1131_;
v___y_1114_ = v___y_1128_;
v___y_1115_ = v___x_1133_;
v___y_1116_ = v___y_1129_;
v___y_1117_ = v___y_1130_;
v_a_1118_ = v___x_1135_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1134_, v___x_1138_, v___x_1139_, v___x_1137_, v___y_1131_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_dec_ref_known(v___x_1140_, 1);
v___y_1113_ = v___y_1131_;
v___y_1114_ = v___y_1128_;
v___y_1115_ = v___x_1133_;
v___y_1116_ = v___y_1129_;
v___y_1117_ = v___y_1130_;
v_a_1118_ = v___x_1135_;
goto v___jp_1112_;
}
else
{
lean_dec_ref(v___x_1133_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___x_1140_;
}
}
}
v___jp_1141_:
{
if (v_a_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1149_ = lean_box(v_tmp_903_);
v___x_1150_ = lean_obj_tag_nat(v___x_1149_);
lean_dec(v___x_1149_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_dec_eq(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1144_);
v___x_1154_ = l_IO_FS_writeFile(v___y_1143_, v___x_1153_);
lean_dec_ref(v___x_1153_);
lean_dec_ref(v___y_1143_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_dec_ref_known(v___x_1154_, 1);
v___y_1128_ = v___y_1145_;
v___y_1129_ = v___y_1146_;
v___y_1130_ = v___y_1147_;
v___y_1131_ = v___y_1142_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1159_ = lean_io_error_to_string(v_a_1155_);
v___x_1160_ = 3;
v___x_1161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*1, v___x_1160_);
lean_inc_ref(v___y_1142_);
v___x_1162_ = lean_apply_2(v___y_1142_, v___x_1161_, lean_box(0));
v___x_1163_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1163_);
v___x_1165_ = v___x_1157_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v___y_1144_);
v___x_1168_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1169_ = l_IO_FS_writeFile(v___y_1143_, v___x_1168_);
lean_dec_ref(v___y_1143_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_dec_ref_known(v___x_1169_, 1);
v___y_1128_ = v___y_1145_;
v___y_1129_ = v___y_1146_;
v___y_1130_ = v___y_1147_;
v___y_1131_ = v___y_1142_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1182_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1182_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1174_ = lean_io_error_to_string(v_a_1170_);
v___x_1175_ = 3;
v___x_1176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*1, v___x_1175_);
lean_inc_ref(v___y_1142_);
v___x_1177_ = lean_apply_2(v___y_1142_, v___x_1176_, lean_box(0));
v___x_1178_ = lean_box(0);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1178_);
v___x_1180_ = v___x_1172_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
v___y_1128_ = v___y_1145_;
v___y_1129_ = v___y_1146_;
v___y_1130_ = v___y_1147_;
v___y_1131_ = v___y_1142_;
goto v___jp_1127_;
}
}
v___jp_1183_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1189_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_901_);
v___x_1190_ = l_Lake_joinRelative(v_dir_901_, v___x_1189_);
v___x_1191_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1192_ = l_System_FilePath_pathExists(v___x_1190_);
v___x_1193_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1193_ == 0)
{
v___y_1142_ = v___y_1184_;
v___y_1143_ = v___x_1190_;
v___y_1144_ = v___y_1185_;
v___y_1145_ = v___y_1186_;
v___y_1146_ = v___y_1187_;
v___y_1147_ = v___y_1188_;
v_a_1148_ = v___x_1192_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1191_, v___x_1195_, v___x_1196_, v___x_1194_, v___y_1184_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_dec_ref_known(v___x_1197_, 1);
v___y_1142_ = v___y_1184_;
v___y_1143_ = v___x_1190_;
v___y_1144_ = v___y_1185_;
v___y_1145_ = v___y_1186_;
v___y_1146_ = v___y_1187_;
v___y_1147_ = v___y_1188_;
v_a_1148_ = v___x_1192_;
goto v___jp_1141_;
}
else
{
lean_dec_ref(v___x_1190_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___x_1197_;
}
}
}
v___jp_1198_:
{
switch(v_tmp_903_)
{
case 0:
{
v___y_1184_ = v___y_1203_;
v___y_1185_ = v___y_1199_;
v___y_1186_ = v___y_1200_;
v___y_1187_ = v___y_1201_;
v___y_1188_ = v___y_1202_;
goto v___jp_1183_;
}
case 1:
{
v___y_1184_ = v___y_1203_;
v___y_1185_ = v___y_1199_;
v___y_1186_ = v___y_1200_;
v___y_1187_ = v___y_1201_;
v___y_1188_ = v___y_1202_;
goto v___jp_1183_;
}
default: 
{
lean_dec(v___y_1199_);
v___y_1128_ = v___y_1200_;
v___y_1129_ = v___y_1201_;
v___y_1130_ = v___y_1202_;
v___y_1131_ = v___y_1203_;
goto v___jp_1127_;
}
}
}
v___jp_1204_:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_IO_FS_writeFile(v___y_1208_, v___y_1211_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1208_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_dec_ref_known(v___x_1212_, 1);
v___y_1199_ = v___y_1206_;
v___y_1200_ = v___y_1207_;
v___y_1201_ = v___y_1209_;
v___y_1202_ = v___y_1210_;
v___y_1203_ = v___y_1205_;
goto v___jp_1198_;
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1217_ = lean_io_error_to_string(v_a_1213_);
v___x_1218_ = 3;
v___x_1219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*1, v___x_1218_);
lean_inc_ref(v___y_1205_);
v___x_1220_ = lean_apply_2(v___y_1205_, v___x_1219_, lean_box(0));
v___x_1221_ = lean_box(0);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1221_);
v___x_1223_ = v___x_1215_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
v___jp_1226_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1233_ = lean_box(v_tmp_903_);
v___x_1234_ = lean_obj_tag_nat(v___x_1233_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_unsigned_to_nat(4u);
v___x_1236_ = lean_nat_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = 1;
lean_inc_n(v___y_1227_, 2);
v___x_1238_ = l_Lean_Name_toString(v___y_1227_, v___x_1237_);
v___x_1239_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1238_, v___y_1227_);
lean_dec_ref(v___x_1238_);
v___y_1205_ = v___y_1232_;
v___y_1206_ = v___y_1227_;
v___y_1207_ = v___y_1229_;
v___y_1208_ = v___y_1228_;
v___y_1209_ = v___y_1230_;
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___x_1239_;
goto v___jp_1204_;
}
else
{
lean_object* v___x_1240_; 
lean_inc(v___y_1227_);
v___x_1240_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1227_);
v___y_1205_ = v___y_1232_;
v___y_1206_ = v___y_1227_;
v___y_1207_ = v___y_1229_;
v___y_1208_ = v___y_1228_;
v___y_1209_ = v___y_1230_;
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___x_1240_;
goto v___jp_1204_;
}
}
v___jp_1241_:
{
if (v_a_1249_ == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = l_IO_FS_createDirAll(v___y_1243_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref_known(v___x_1250_, 1);
v___x_1251_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1252_ = l_IO_FS_writeFile(v___y_1248_, v___x_1251_);
lean_dec_ref(v___y_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_dec_ref_known(v___x_1252_, 1);
v___y_1227_ = v___y_1242_;
v___y_1228_ = v___y_1245_;
v___y_1229_ = v___y_1244_;
v___y_1230_ = v___y_1246_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v_a_907_;
goto v___jp_1226_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1242_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1265_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1265_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1257_ = lean_io_error_to_string(v_a_1253_);
v___x_1258_ = 3;
v___x_1259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*1, v___x_1258_);
lean_inc_ref(v_a_907_);
v___x_1260_ = lean_apply_2(v_a_907_, v___x_1259_, lean_box(0));
v___x_1261_ = lean_box(0);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1261_);
v___x_1263_ = v___x_1255_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1242_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_a_1266_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1268_ = v___x_1250_;
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1250_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1270_ = lean_io_error_to_string(v_a_1266_);
v___x_1271_ = 3;
v___x_1272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*1, v___x_1271_);
lean_inc_ref(v_a_907_);
v___x_1273_ = lean_apply_2(v_a_907_, v___x_1272_, lean_box(0));
v___x_1274_ = lean_box(0);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1274_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_dec_ref(v___y_1248_);
lean_dec_ref(v___y_1243_);
v___y_1227_ = v___y_1242_;
v___y_1228_ = v___y_1245_;
v___y_1229_ = v___y_1244_;
v___y_1230_ = v___y_1246_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v_a_907_;
goto v___jp_1226_;
}
}
v___jp_1282_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_inc(v___y_1287_);
lean_inc(v___y_1283_);
lean_inc(v_name_902_);
v___x_1288_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_903_, v_lang_904_, v_name_902_, v___y_1283_, v___y_1287_);
v___x_1289_ = l_IO_FS_writeFile(v_configFile_1281_, v___x_1288_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v_configFile_1281_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
if (lean_obj_tag(v___y_1286_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; uint8_t v___x_1297_; 
v_val_1290_ = lean_ctor_get(v___y_1286_, 0);
lean_inc_n(v_val_1290_, 2);
lean_dec_ref_known(v___y_1286_, 1);
v___x_1291_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1292_ = l_System_FilePath_withExtension(v_val_1290_, v___x_1291_);
v___x_1293_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v___x_1292_);
v___x_1294_ = l_Lake_joinRelative(v___x_1292_, v___x_1293_);
v___x_1295_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1296_ = l_System_FilePath_pathExists(v___x_1294_);
v___x_1297_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1297_ == 0)
{
v___y_1242_ = v___y_1283_;
v___y_1243_ = v___x_1292_;
v___y_1244_ = v___y_1284_;
v___y_1245_ = v_val_1290_;
v___y_1246_ = v___y_1285_;
v___y_1247_ = v___y_1287_;
v___y_1248_ = v___x_1294_;
v_a_1249_ = v___x_1296_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_box(0);
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1295_, v___x_1299_, v___x_1300_, v___x_1298_, v_a_907_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_dec_ref_known(v___x_1301_, 1);
v___y_1242_ = v___y_1283_;
v___y_1243_ = v___x_1292_;
v___y_1244_ = v___y_1284_;
v___y_1245_ = v_val_1290_;
v___y_1246_ = v___y_1285_;
v___y_1247_ = v___y_1287_;
v___y_1248_ = v___x_1294_;
v_a_1249_ = v___x_1296_;
goto v___jp_1241_;
}
else
{
lean_dec_ref(v___x_1294_);
lean_dec_ref(v___x_1292_);
lean_dec(v_val_1290_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___x_1301_;
}
}
}
else
{
lean_dec(v___y_1286_);
v___y_1199_ = v___y_1283_;
v___y_1200_ = v___y_1284_;
v___y_1201_ = v___y_1285_;
v___y_1202_ = v___y_1287_;
v___y_1203_ = v_a_907_;
goto v___jp_1198_;
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_a_1302_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1304_ = v___x_1289_;
v_isShared_1305_ = v_isSharedCheck_1314_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1289_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1314_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1306_ = lean_io_error_to_string(v_a_1302_);
v___x_1307_ = 3;
v___x_1308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*1, v___x_1307_);
lean_inc_ref(v_a_907_);
v___x_1309_ = lean_apply_2(v_a_907_, v___x_1308_, lean_box(0));
v___x_1310_ = lean_box(0);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1310_);
v___x_1312_ = v___x_1304_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1315_:
{
lean_object* v_lean_1318_; lean_object* v_toolchain_1319_; lean_object* v___x_1320_; 
v_lean_1318_ = lean_ctor_get(v_env_905_, 1);
v_toolchain_1319_ = lean_ctor_get(v_env_905_, 19);
lean_inc_ref(v_toolchain_1319_);
v___x_1320_ = l_Lake_ToolchainVer_ofString(v_toolchain_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_ver_1321_; lean_object* v___x_1322_; 
v_ver_1321_ = lean_ctor_get(v___x_1320_, 1);
lean_inc_ref(v_ver_1321_);
lean_dec_ref_known(v___x_1320_, 2);
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_ver_1321_);
lean_inc_ref(v_toolchain_1319_);
lean_inc_ref(v_lean_1318_);
v___y_1283_ = v_fst_1316_;
v___y_1284_ = v_lean_1318_;
v___y_1285_ = v_toolchain_1319_;
v___y_1286_ = v_snd_1317_;
v___y_1287_ = v___x_1322_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v___x_1320_);
v___x_1323_ = lean_box(0);
lean_inc_ref(v_toolchain_1319_);
lean_inc_ref(v_lean_1318_);
v___y_1283_ = v_fst_1316_;
v___y_1284_ = v_lean_1318_;
v___y_1285_ = v_toolchain_1319_;
v___y_1286_ = v_snd_1317_;
v___y_1287_ = v___x_1323_;
goto v___jp_1282_;
}
}
v___jp_1324_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_box(0);
lean_inc(v_name_902_);
v_fst_1316_ = v_name_902_;
v_snd_1317_ = v___x_1325_;
goto v___jp_1315_;
}
v___jp_1326_:
{
if (v_a_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___y_1328_);
v_fst_1316_ = v___y_1327_;
v_snd_1317_ = v___x_1330_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v___y_1328_);
v___x_1331_ = lean_box(0);
v_fst_1316_ = v___y_1327_;
v_snd_1317_ = v___x_1331_;
goto v___jp_1315_;
}
}
v___jp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1335_ = lean_box(v_tmp_903_);
v___x_1336_ = lean_obj_tag_nat(v___x_1335_);
lean_dec(v___x_1335_);
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_dec_eq(v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
if (v_a_1334_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; uint8_t v___x_1343_; 
lean_inc(v_name_902_);
v___x_1339_ = l_Lake_toUpperCamelCase(v_name_902_);
lean_inc(v___x_1339_);
v___x_1340_ = l_Lean_modToFilePath(v_dir_901_, v___x_1339_, v___y_1333_);
v___x_1341_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1342_ = l_System_FilePath_pathExists(v___x_1340_);
v___x_1343_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1343_ == 0)
{
v___y_1327_ = v___x_1339_;
v___y_1328_ = v___x_1340_;
v_a_1329_ = v___x_1342_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1341_, v___x_1345_, v___x_1346_, v___x_1344_, v_a_907_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_dec_ref_known(v___x_1347_, 1);
v___y_1327_ = v___x_1339_;
v___y_1328_ = v___x_1340_;
v_a_1329_ = v___x_1342_;
goto v___jp_1326_;
}
else
{
lean_dec_ref(v___x_1340_);
lean_dec(v___x_1339_);
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___x_1347_;
}
}
}
else
{
goto v___jp_1324_;
}
}
else
{
goto v___jp_1324_;
}
}
v___jp_1348_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; 
v___x_1349_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc(v_name_902_);
v___x_1350_ = l_Lean_modToFilePath(v_dir_901_, v_name_902_, v___x_1349_);
v___x_1351_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1352_ = l_System_FilePath_pathExists(v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1353_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1353_ == 0)
{
v___y_1333_ = v___x_1349_;
v_a_1334_ = v___x_1352_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1351_, v___x_1355_, v___x_1356_, v___x_1354_, v_a_907_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v___y_1333_ = v___x_1349_;
v_a_1334_ = v___x_1352_;
goto v___jp_1332_;
}
else
{
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___x_1357_;
}
}
}
v___jp_1358_:
{
if (lean_obj_tag(v___y_1359_) == 0)
{
lean_dec_ref_known(v___y_1359_, 1);
goto v___jp_1348_;
}
else
{
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
return v___y_1359_;
}
}
v___jp_1360_:
{
if (v_a_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_901_);
v___x_1364_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_901_, v_tmp_903_, v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 1);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 2);
v___x_1366_ = lean_array_get_size(v_a_1365_);
v___x_1367_ = lean_nat_dec_lt(v___x_1362_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_dec(v_a_1365_);
goto v___jp_1348_;
}
else
{
lean_object* v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1366_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1365_, v___x_1369_, v___x_1370_, v___x_1368_, v_a_907_);
lean_dec(v_a_1365_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_dec_ref_known(v___x_1371_, 1);
goto v___jp_1348_;
}
else
{
v___y_1359_ = v___x_1371_;
goto v___jp_1358_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_a_1372_ = lean_ctor_get(v___x_1364_, 1);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1364_, 2);
v___x_1373_ = lean_array_get_size(v_a_1372_);
v___x_1374_ = lean_nat_dec_lt(v___x_1362_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_a_1372_);
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = lean_usize_of_nat(v___x_1373_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1372_, v___x_1378_, v___x_1379_, v___x_1377_, v_a_907_);
lean_dec(v_a_1372_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___x_1380_, 0);
lean_dec(v_unused_1388_);
v___x_1382_ = v___x_1380_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v___x_1380_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 1);
lean_ctor_set(v___x_1382_, 0, v___x_1377_);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1377_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
v___y_1359_ = v___x_1380_;
goto v___jp_1358_;
}
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_configFile_1281_);
lean_dec_ref(v_env_905_);
lean_dec(v_name_902_);
lean_dec_ref(v_dir_901_);
v___x_1389_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17));
lean_inc_ref(v_a_907_);
v___x_1390_ = lean_apply_2(v_a_907_, v___x_1389_, lean_box(0));
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* v_dir_1400_, lean_object* v_name_1401_, lean_object* v_tmp_1402_, lean_object* v_lang_1403_, lean_object* v_env_1404_, lean_object* v_offline_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
uint8_t v_tmp_boxed_1408_; uint8_t v_lang_boxed_1409_; uint8_t v_offline_boxed_1410_; lean_object* v_res_1411_; 
v_tmp_boxed_1408_ = lean_unbox(v_tmp_1402_);
v_lang_boxed_1409_ = lean_unbox(v_lang_1403_);
v_offline_boxed_1410_ = lean_unbox(v_offline_1405_);
v_res_1411_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_1400_, v_name_1401_, v_tmp_boxed_1408_, v_lang_boxed_1409_, v_env_1404_, v_offline_boxed_1410_, v_a_1406_);
lean_dec_ref(v_a_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(lean_object* v_a_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = 0;
return v___x_1414_;
}
else
{
lean_object* v_head_1415_; lean_object* v_tail_1416_; uint8_t v___x_1417_; 
v_head_1415_ = lean_ctor_get(v_x_1413_, 0);
v_tail_1416_ = lean_ctor_get(v_x_1413_, 1);
v___x_1417_ = lean_string_dec_eq(v_a_1412_, v_head_1415_);
if (v___x_1417_ == 0)
{
v_x_1413_ = v_tail_1416_;
goto _start;
}
else
{
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3___boxed(lean_object* v_a_1419_, lean_object* v_x_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v_a_1419_, v_x_1420_);
lean_dec(v_x_1420_);
lean_dec_ref(v_a_1419_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* v_s_1423_, lean_object* v_pos_1424_){
_start:
{
lean_object* v_str_1425_; lean_object* v_startInclusive_1426_; lean_object* v_endExclusive_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v_decide_1431_; 
v_str_1425_ = lean_ctor_get(v_s_1423_, 0);
v_startInclusive_1426_ = lean_ctor_get(v_s_1423_, 1);
v_endExclusive_1427_ = lean_ctor_get(v_s_1423_, 2);
v___x_1428_ = lean_nat_add(v_startInclusive_1426_, v_pos_1424_);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_nat_sub(v_endExclusive_1427_, v___x_1428_);
v_decide_1431_ = lean_nat_dec_eq(v___x_1429_, v___x_1430_);
lean_dec(v___x_1430_);
if (v_decide_1431_ == 0)
{
uint32_t v___x_1432_; uint32_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_string_utf8_get_fast(v_str_1425_, v___x_1428_);
v___x_1433_ = 46;
v___x_1434_ = lean_uint32_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_dec(v___x_1428_);
return v_pos_1424_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1435_ = lean_string_utf8_next_fast(v_str_1425_, v___x_1428_);
v___x_1436_ = lean_nat_sub(v___x_1435_, v___x_1428_);
lean_dec(v___x_1428_);
v___x_1437_ = lean_nat_add(v_pos_1424_, v___x_1436_);
lean_dec(v___x_1436_);
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_add(v_pos_1424_, v___x_1438_);
v___x_1440_ = lean_nat_dec_le(v___x_1439_, v___x_1437_);
lean_dec(v___x_1439_);
if (v___x_1440_ == 0)
{
lean_dec(v___x_1437_);
return v_pos_1424_;
}
else
{
lean_dec(v_pos_1424_);
v_pos_1424_ = v___x_1437_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1428_);
return v_pos_1424_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* v_s_1442_, lean_object* v_pos_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_1442_, v_pos_1443_);
lean_dec_ref(v_s_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(uint32_t v_a_1445_, lean_object* v_x_1446_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
uint8_t v___x_1447_; 
v___x_1447_ = 0;
return v___x_1447_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; uint32_t v___x_1450_; uint8_t v___x_1451_; 
v_head_1448_ = lean_ctor_get(v_x_1446_, 0);
v_tail_1449_ = lean_ctor_get(v_x_1446_, 1);
v___x_1450_ = lean_unbox_uint32(v_head_1448_);
v___x_1451_ = lean_uint32_dec_eq(v_a_1445_, v___x_1450_);
if (v___x_1451_ == 0)
{
v_x_1446_ = v_tail_1449_;
goto _start;
}
else
{
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
uint32_t v_a_boxed_1455_; uint8_t v_res_1456_; lean_object* v_r_1457_; 
v_a_boxed_1455_ = lean_unbox_uint32(v_a_1453_);
lean_dec(v_a_1453_);
v_res_1456_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_a_boxed_1455_, v_x_1454_);
lean_dec(v_x_1454_);
v_r_1457_ = lean_box(v_res_1456_);
return v_r_1457_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = 92;
v___x_1459_ = lean_box_uint32(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_box(0);
v___x_1461_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1;
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___x_1460_);
return v___x_1462_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = 47;
v___x_1464_ = lean_box_uint32(v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0);
v___x_1466_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1;
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(lean_object* v_s_1468_, lean_object* v_a_1469_, uint8_t v_b_1470_){
_start:
{
lean_object* v_str_1471_; lean_object* v_startInclusive_1472_; lean_object* v_endExclusive_1473_; lean_object* v___x_1474_; uint8_t v_decide_1475_; 
v_str_1471_ = lean_ctor_get(v_s_1468_, 0);
v_startInclusive_1472_ = lean_ctor_get(v_s_1468_, 1);
v_endExclusive_1473_ = lean_ctor_get(v_s_1468_, 2);
v___x_1474_ = lean_nat_sub(v_endExclusive_1473_, v_startInclusive_1472_);
v_decide_1475_ = lean_nat_dec_eq(v_a_1469_, v___x_1474_);
lean_dec(v___x_1474_);
if (v_decide_1475_ == 0)
{
lean_object* v___x_1476_; uint32_t v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1476_ = lean_nat_add(v_startInclusive_1472_, v_a_1469_);
lean_dec(v_a_1469_);
v___x_1477_ = lean_string_utf8_get_fast(v_str_1471_, v___x_1476_);
v___x_1478_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1);
v___x_1479_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_string_utf8_next_fast(v_str_1471_, v___x_1476_);
lean_dec(v___x_1476_);
v___x_1481_ = lean_nat_sub(v___x_1480_, v_startInclusive_1472_);
v_a_1469_ = v___x_1481_;
v_b_1470_ = v___x_1479_;
goto _start;
}
else
{
lean_dec(v___x_1476_);
return v___x_1479_;
}
}
else
{
lean_dec(v_a_1469_);
return v_b_1470_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___boxed(lean_object* v_s_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_){
_start:
{
uint8_t v_b_boxed_1486_; uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_b_boxed_1486_ = lean_unbox(v_b_1485_);
v_res_1487_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1483_, v_a_1484_, v_b_boxed_1486_);
lean_dec_ref(v_s_1483_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object* v_s_1489_){
_start:
{
lean_object* v_searcher_1490_; uint8_t v___x_1491_; uint8_t v___x_1492_; 
v_searcher_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = 0;
v___x_1492_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1489_, v_searcher_1490_, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object* v_s_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v_s_1493_);
lean_dec_ref(v_s_1493_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* v_pkgName_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_string_utf8_byte_size(v_pkgName_1516_);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_nat_dec_eq(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v_decide_1534_; 
lean_inc_ref(v_pkgName_1516_);
v___x_1532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1532_, 0, v_pkgName_1516_);
lean_ctor_set(v___x_1532_, 1, v___x_1530_);
lean_ctor_set(v___x_1532_, 2, v___x_1529_);
v___x_1533_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_1532_, v___x_1530_);
v_decide_1534_ = lean_nat_dec_eq(v___x_1533_, v___x_1529_);
lean_dec(v___x_1533_);
if (v_decide_1534_ == 0)
{
uint8_t v___x_1535_; 
v___x_1535_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(v___x_1532_);
lean_dec_ref_known(v___x_1532_, 3);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_1516_, v___x_1530_);
v___x_1537_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7));
v___x_1538_ = l_List_elem___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__3(v___x_1536_, v___x_1537_);
lean_dec_ref(v___x_1536_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_a_1517_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9));
v___x_1542_ = lean_array_get_size(v_a_1517_);
v___x_1543_ = lean_array_push(v_a_1517_, v___x_1541_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
return v___x_1544_;
}
}
else
{
goto v___jp_1519_;
}
}
else
{
lean_dec_ref_known(v___x_1532_, 3);
goto v___jp_1519_;
}
}
else
{
goto v___jp_1519_;
}
v___jp_1519_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1520_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
v___x_1521_ = lean_string_append(v___x_1520_, v_pkgName_1516_);
lean_dec_ref(v_pkgName_1516_);
v___x_1522_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_1523_ = lean_string_append(v___x_1521_, v___x_1522_);
v___x_1524_ = 3;
v___x_1525_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*1, v___x_1524_);
v___x_1526_ = lean_array_get_size(v_a_1517_);
v___x_1527_ = lean_array_push(v_a_1517_, v___x_1525_);
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* v_pkgName_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1545_, v_a_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object* v_s_1549_, lean_object* v_inst_1550_, lean_object* v_R_1551_, lean_object* v_a_1552_, uint8_t v_b_1553_, lean_object* v_c_1554_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg(v_s_1549_, v_a_1552_, v_b_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object* v_s_1556_, lean_object* v_inst_1557_, lean_object* v_R_1558_, lean_object* v_a_1559_, lean_object* v_b_1560_, lean_object* v_c_1561_){
_start:
{
uint8_t v_b_boxed_1562_; uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_b_boxed_1562_ = lean_unbox(v_b_1560_);
v_res_1563_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(v_s_1556_, v_inst_1557_, v_R_1558_, v_a_1559_, v_b_boxed_1562_, v_c_1561_);
lean_dec_ref(v_s_1556_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* v_a_1565_, lean_object* v_dir_1566_, lean_object* v_name_1567_, uint8_t v_tmp_1568_, uint8_t v_lang_1569_, lean_object* v_env_1570_, uint8_t v_offline_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___y_1575_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1603_; lean_object* v___y_1604_; uint8_t v_a_1605_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; uint8_t v_a_1725_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; uint8_t v_a_1782_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; uint8_t v_a_1812_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v_a_1913_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_configFile_1945_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v_fst_1980_; lean_object* v_snd_1981_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v_a_1993_; lean_object* v___y_1997_; uint8_t v_a_1998_; lean_object* v___y_2023_; uint8_t v_a_2025_; lean_object* v___x_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; 
v___x_1573_ = l_Lake_defaultConfigFile;
v___x_1943_ = l_Lake_ConfigLang_fileExtension(v_lang_1569_);
v___x_1944_ = l_System_FilePath_addExtension(v___x_1573_, v___x_1943_);
lean_dec_ref(v___x_1943_);
lean_inc_ref(v_dir_1566_);
v_configFile_1945_ = l_Lake_joinRelative(v_dir_1566_, v___x_1944_);
v___x_2057_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2058_ = l_System_FilePath_pathExists(v_configFile_1945_);
v___x_2059_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2059_ == 0)
{
v_a_2025_ = v___x_2058_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = lean_box(0);
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2057_, v___x_2061_, v___x_2062_, v___x_2060_, v_a_1565_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_dec_ref_known(v___x_2063_, 1);
v_a_2025_ = v___x_2058_;
goto v___jp_2024_;
}
else
{
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_2063_;
}
}
v___jp_1574_:
{
if (v_offline_1571_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_box(0);
v___x_1579_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_1566_);
v___x_1580_ = l_Lake_joinRelative(v_dir_1566_, v___x_1579_);
lean_inc_ref(v___x_1580_);
v___x_1581_ = l_Lake_joinRelative(v___x_1580_, v___x_1573_);
v___x_1582_ = l_Lake_defaultManifestFile;
v___x_1583_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_1584_ = lean_box(1);
v___x_1585_ = l_Lean_Options_empty;
v___x_1586_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1587_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_1587_, 0, v_env_1570_);
lean_ctor_set(v___x_1587_, 1, v___x_1576_);
lean_ctor_set(v___x_1587_, 2, v_dir_1566_);
lean_ctor_set(v___x_1587_, 3, v___x_1577_);
lean_ctor_set(v___x_1587_, 4, v___x_1578_);
lean_ctor_set(v___x_1587_, 5, v___x_1579_);
lean_ctor_set(v___x_1587_, 6, v___x_1580_);
lean_ctor_set(v___x_1587_, 7, v___x_1573_);
lean_ctor_set(v___x_1587_, 8, v___x_1581_);
lean_ctor_set(v___x_1587_, 9, v___x_1576_);
lean_ctor_set(v___x_1587_, 10, v___x_1582_);
lean_ctor_set(v___x_1587_, 11, v___x_1583_);
lean_ctor_set(v___x_1587_, 12, v___x_1584_);
lean_ctor_set(v___x_1587_, 13, v___x_1585_);
lean_ctor_set(v___x_1587_, 14, v___x_1586_);
lean_ctor_set(v___x_1587_, 15, v___x_1586_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*16, v_offline_1571_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*16 + 1, v_offline_1571_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*16 + 2, v_offline_1571_);
v___x_1588_ = l_Lean_NameSet_empty;
v___x_1589_ = l_Lake_updateManifest(v___x_1587_, v___x_1588_, v___y_1575_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
v___jp_1592_:
{
if (lean_obj_tag(v___y_1594_) == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_1593_);
v___x_1596_ = lean_apply_2(v___y_1593_, v___x_1595_, lean_box(0));
v___y_1575_ = v___y_1593_;
goto v___jp_1574_;
}
else
{
lean_dec_ref_known(v___y_1594_, 1);
v___y_1575_ = v___y_1593_;
goto v___jp_1574_;
}
}
v___jp_1597_:
{
switch(v_tmp_1568_)
{
case 3:
{
v___y_1593_ = v___y_1599_;
v___y_1594_ = v___y_1598_;
goto v___jp_1592_;
}
case 4:
{
v___y_1593_ = v___y_1599_;
v___y_1594_ = v___y_1598_;
goto v___jp_1592_;
}
default: 
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v___y_1598_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
}
v___jp_1602_:
{
if (v_a_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_1603_);
v___x_1607_ = lean_apply_2(v___y_1603_, v___x_1606_, lean_box(0));
v___y_1598_ = v___y_1604_;
v___y_1599_ = v___y_1603_;
goto v___jp_1597_;
}
else
{
v___y_1598_ = v___y_1604_;
v___y_1599_ = v___y_1603_;
goto v___jp_1597_;
}
}
v___jp_1608_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; 
v___x_1613_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_1566_);
v___x_1614_ = l_Lake_joinRelative(v_dir_1566_, v___x_1613_);
v___x_1615_ = 4;
v___x_1616_ = lean_io_prim_handle_mk(v___x_1614_, v___x_1615_);
lean_dec_ref(v___x_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_1619_ = lean_io_prim_handle_put_str(v_a_1617_, v___x_1618_);
lean_dec(v_a_1617_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
lean_dec_ref_known(v___x_1619_, 1);
v___x_1620_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1566_);
v___x_1621_ = l_Lake_joinRelative(v_dir_1566_, v___x_1620_);
v___x_1622_ = lean_string_utf8_byte_size(v___y_1610_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_nat_dec_eq(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v___y_1609_);
v___x_1625_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1626_ = lean_string_append(v___y_1610_, v___x_1625_);
v___x_1627_ = l_IO_FS_writeFile(v___x_1621_, v___x_1626_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1621_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
v___y_1598_ = v___y_1611_;
v___y_1599_ = v___y_1612_;
goto v___jp_1597_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v___y_1611_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1640_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1640_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1632_ = lean_io_error_to_string(v_a_1628_);
v___x_1633_ = 3;
v___x_1634_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*1, v___x_1633_);
lean_inc_ref(v___y_1612_);
v___x_1635_ = lean_apply_2(v___y_1612_, v___x_1634_, lean_box(0));
v___x_1636_ = lean_box(0);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1636_);
v___x_1638_ = v___x_1630_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_githash_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
lean_dec_ref(v___y_1610_);
v_githash_1641_ = lean_ctor_get(v___y_1609_, 1);
lean_inc_ref(v_githash_1641_);
lean_dec_ref(v___y_1609_);
v___x_1642_ = lean_string_utf8_byte_size(v_githash_1641_);
lean_dec_ref(v_githash_1641_);
v___x_1643_ = lean_nat_dec_eq(v___x_1642_, v___x_1623_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; uint8_t v___x_1645_; uint8_t v___x_1646_; 
v___x_1644_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1645_ = l_System_FilePath_pathExists(v___x_1621_);
lean_dec_ref(v___x_1621_);
v___x_1646_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1646_ == 0)
{
v___y_1603_ = v___y_1612_;
v___y_1604_ = v___y_1611_;
v_a_1605_ = v___x_1645_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = lean_box(0);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1644_, v___x_1648_, v___x_1649_, v___x_1647_, v___y_1612_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_dec_ref_known(v___x_1650_, 1);
v___y_1603_ = v___y_1612_;
v___y_1604_ = v___y_1611_;
v_a_1605_ = v___x_1645_;
goto v___jp_1602_;
}
else
{
lean_dec(v___y_1611_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
return v___x_1650_;
}
}
}
else
{
lean_dec_ref(v___x_1621_);
v___y_1598_ = v___y_1611_;
v___y_1599_ = v___y_1612_;
goto v___jp_1597_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
v_a_1651_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1653_ = v___x_1619_;
v_isShared_1654_ = v_isSharedCheck_1663_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1619_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1663_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1655_ = lean_io_error_to_string(v_a_1651_);
v___x_1656_ = 3;
v___x_1657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set_uint8(v___x_1657_, sizeof(void*)*1, v___x_1656_);
lean_inc_ref(v___y_1612_);
v___x_1658_ = lean_apply_2(v___y_1612_, v___x_1657_, lean_box(0));
v___x_1659_ = lean_box(0);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1659_);
v___x_1661_ = v___x_1653_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
v_a_1664_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1666_ = v___x_1616_;
v_isShared_1667_ = v_isSharedCheck_1676_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1616_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1676_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1668_ = lean_io_error_to_string(v_a_1664_);
v___x_1669_ = 3;
v___x_1670_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*1, v___x_1669_);
lean_inc_ref(v___y_1612_);
v___x_1671_ = lean_apply_2(v___y_1612_, v___x_1670_, lean_box(0));
v___x_1672_ = lean_box(0);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1672_);
v___x_1674_ = v___x_1666_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
v___jp_1677_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1678_);
v___x_1683_ = lean_apply_2(v___y_1678_, v___x_1682_, lean_box(0));
v___y_1609_ = v___y_1679_;
v___y_1610_ = v___y_1681_;
v___y_1611_ = v___y_1680_;
v___y_1612_ = v___y_1678_;
goto v___jp_1608_;
}
v___jp_1684_:
{
if (lean_obj_tag(v___y_1689_) == 0)
{
lean_dec_ref_known(v___y_1689_, 1);
v___y_1609_ = v___y_1686_;
v___y_1610_ = v___y_1688_;
v___y_1611_ = v___y_1687_;
v___y_1612_ = v___y_1685_;
goto v___jp_1608_;
}
else
{
lean_dec_ref_known(v___y_1689_, 1);
v___y_1678_ = v___y_1685_;
v___y_1679_ = v___y_1686_;
v___y_1680_ = v___y_1687_;
v___y_1681_ = v___y_1688_;
goto v___jp_1677_;
}
}
v___jp_1690_:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = l_Lake_Git_upstreamBranch;
v___x_1696_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1566_);
v___x_1699_ = l_Lake_GitRepo_checkoutBranch(v___x_1695_, v_dir_1566_, v___x_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 1);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 2);
v___x_1701_ = lean_array_get_size(v_a_1700_);
v___x_1702_ = lean_nat_dec_lt(v___x_1697_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_dec(v_a_1700_);
v___y_1609_ = v___y_1692_;
v___y_1610_ = v___y_1694_;
v___y_1611_ = v___y_1693_;
v___y_1612_ = v___y_1691_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = lean_usize_of_nat(v___x_1701_);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1700_, v___x_1704_, v___x_1705_, v___x_1703_, v___y_1691_);
lean_dec(v_a_1700_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_dec_ref_known(v___x_1706_, 1);
v___y_1609_ = v___y_1692_;
v___y_1610_ = v___y_1694_;
v___y_1611_ = v___y_1693_;
v___y_1612_ = v___y_1691_;
goto v___jp_1608_;
}
else
{
v___y_1685_ = v___y_1691_;
v___y_1686_ = v___y_1692_;
v___y_1687_ = v___y_1693_;
v___y_1688_ = v___y_1694_;
v___y_1689_ = v___x_1706_;
goto v___jp_1684_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_a_1707_ = lean_ctor_get(v___x_1699_, 1);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1699_, 2);
v___x_1708_ = lean_array_get_size(v_a_1707_);
v___x_1709_ = lean_nat_dec_lt(v___x_1697_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec(v_a_1707_);
v___y_1678_ = v___y_1691_;
v___y_1679_ = v___y_1692_;
v___y_1680_ = v___y_1693_;
v___y_1681_ = v___y_1694_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = lean_usize_of_nat(v___x_1708_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1707_, v___x_1711_, v___x_1712_, v___x_1710_, v___y_1691_);
lean_dec(v_a_1707_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec_ref_known(v___x_1713_, 1);
v___y_1678_ = v___y_1691_;
v___y_1679_ = v___y_1692_;
v___y_1680_ = v___y_1693_;
v___y_1681_ = v___y_1694_;
goto v___jp_1677_;
}
else
{
v___y_1685_ = v___y_1691_;
v___y_1686_ = v___y_1692_;
v___y_1687_ = v___y_1693_;
v___y_1688_ = v___y_1694_;
v___y_1689_ = v___x_1713_;
goto v___jp_1684_;
}
}
}
}
else
{
v___y_1609_ = v___y_1692_;
v___y_1610_ = v___y_1694_;
v___y_1611_ = v___y_1693_;
v___y_1612_ = v___y_1691_;
goto v___jp_1608_;
}
}
v___jp_1714_:
{
if (lean_obj_tag(v___y_1719_) == 0)
{
lean_dec_ref_known(v___y_1719_, 1);
v___y_1691_ = v___y_1715_;
v___y_1692_ = v___y_1716_;
v___y_1693_ = v___y_1718_;
v___y_1694_ = v___y_1717_;
goto v___jp_1690_;
}
else
{
lean_dec_ref_known(v___y_1719_, 1);
v___y_1678_ = v___y_1715_;
v___y_1679_ = v___y_1716_;
v___y_1680_ = v___y_1718_;
v___y_1681_ = v___y_1717_;
goto v___jp_1677_;
}
}
v___jp_1720_:
{
if (v_a_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1566_);
v___x_1728_ = l_Lake_GitRepo_quietInit(v_dir_1566_, v___x_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 1);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 2);
v___x_1730_ = lean_array_get_size(v_a_1729_);
v___x_1731_ = lean_nat_dec_lt(v___x_1726_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_dec(v_a_1729_);
v___y_1691_ = v___y_1721_;
v___y_1692_ = v___y_1722_;
v___y_1693_ = v___y_1724_;
v___y_1694_ = v___y_1723_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_box(0);
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = lean_usize_of_nat(v___x_1730_);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1729_, v___x_1733_, v___x_1734_, v___x_1732_, v___y_1721_);
lean_dec(v_a_1729_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_dec_ref_known(v___x_1735_, 1);
v___y_1691_ = v___y_1721_;
v___y_1692_ = v___y_1722_;
v___y_1693_ = v___y_1724_;
v___y_1694_ = v___y_1723_;
goto v___jp_1690_;
}
else
{
v___y_1715_ = v___y_1721_;
v___y_1716_ = v___y_1722_;
v___y_1717_ = v___y_1723_;
v___y_1718_ = v___y_1724_;
v___y_1719_ = v___x_1735_;
goto v___jp_1714_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1728_, 1);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1728_, 2);
v___x_1737_ = lean_array_get_size(v_a_1736_);
v___x_1738_ = lean_nat_dec_lt(v___x_1726_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_dec(v_a_1736_);
v___y_1678_ = v___y_1721_;
v___y_1679_ = v___y_1722_;
v___y_1680_ = v___y_1724_;
v___y_1681_ = v___y_1723_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = lean_usize_of_nat(v___x_1737_);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1736_, v___x_1740_, v___x_1741_, v___x_1739_, v___y_1721_);
lean_dec(v_a_1736_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_dec_ref_known(v___x_1742_, 1);
v___y_1678_ = v___y_1721_;
v___y_1679_ = v___y_1722_;
v___y_1680_ = v___y_1724_;
v___y_1681_ = v___y_1723_;
goto v___jp_1677_;
}
else
{
v___y_1715_ = v___y_1721_;
v___y_1716_ = v___y_1722_;
v___y_1717_ = v___y_1723_;
v___y_1718_ = v___y_1724_;
v___y_1719_ = v___x_1742_;
goto v___jp_1714_;
}
}
}
}
else
{
v___y_1609_ = v___y_1722_;
v___y_1610_ = v___y_1723_;
v___y_1611_ = v___y_1724_;
v___y_1612_ = v___y_1721_;
goto v___jp_1608_;
}
}
v___jp_1743_:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1566_);
v___x_1749_ = l_Lake_GitRepo_insideWorkTree(v_dir_1566_);
v___x_1750_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1750_ == 0)
{
v___y_1721_ = v___y_1747_;
v___y_1722_ = v___y_1744_;
v___y_1723_ = v___y_1745_;
v___y_1724_ = v___y_1746_;
v_a_1725_ = v___x_1749_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1748_, v___x_1752_, v___x_1753_, v___x_1751_, v___y_1747_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_dec_ref_known(v___x_1754_, 1);
v___y_1721_ = v___y_1747_;
v___y_1722_ = v___y_1744_;
v___y_1723_ = v___y_1745_;
v___y_1724_ = v___y_1746_;
v_a_1725_ = v___x_1749_;
goto v___jp_1720_;
}
else
{
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
return v___x_1754_;
}
}
}
v___jp_1755_:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_IO_FS_writeFile(v___y_1760_, v___y_1761_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_dec_ref_known(v___x_1762_, 1);
v___y_1744_ = v___y_1757_;
v___y_1745_ = v___y_1759_;
v___y_1746_ = v___y_1758_;
v___y_1747_ = v___y_1756_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v_env_1570_);
lean_dec_ref(v_dir_1566_);
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1775_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1775_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1767_ = lean_io_error_to_string(v_a_1763_);
v___x_1768_ = 3;
v___x_1769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*1, v___x_1768_);
lean_inc_ref(v___y_1756_);
v___x_1770_ = lean_apply_2(v___y_1756_, v___x_1769_, lean_box(0));
v___x_1771_ = lean_box(0);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1771_);
v___x_1773_ = v___x_1765_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
v___jp_1776_:
{
if (v_a_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = lean_box(v_tmp_1568_);
v___x_1784_ = lean_obj_tag_nat(v___x_1783_);
lean_dec(v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(4u);
v___x_1786_ = lean_nat_dec_eq(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1567_);
v___x_1788_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1787_);
lean_dec_ref(v___x_1787_);
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1778_;
v___y_1758_ = v___y_1780_;
v___y_1759_ = v___y_1779_;
v___y_1760_ = v___y_1781_;
v___y_1761_ = v___x_1788_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1567_);
v___x_1790_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1789_);
lean_dec_ref(v___x_1789_);
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1778_;
v___y_1758_ = v___y_1780_;
v___y_1759_ = v___y_1779_;
v___y_1760_ = v___y_1781_;
v___y_1761_ = v___x_1790_;
goto v___jp_1755_;
}
}
else
{
lean_dec_ref(v___y_1781_);
lean_dec(v_name_1567_);
v___y_1744_ = v___y_1778_;
v___y_1745_ = v___y_1779_;
v___y_1746_ = v___y_1780_;
v___y_1747_ = v___y_1777_;
goto v___jp_1743_;
}
}
v___jp_1791_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1796_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_1566_);
v___x_1797_ = l_Lake_joinRelative(v_dir_1566_, v___x_1796_);
v___x_1798_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1799_ = l_System_FilePath_pathExists(v___x_1797_);
v___x_1800_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1800_ == 0)
{
v___y_1777_ = v___y_1795_;
v___y_1778_ = v___y_1792_;
v___y_1779_ = v___y_1794_;
v___y_1780_ = v___y_1793_;
v___y_1781_ = v___x_1797_;
v_a_1782_ = v___x_1799_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1798_, v___x_1802_, v___x_1803_, v___x_1801_, v___y_1795_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_dec_ref_known(v___x_1804_, 1);
v___y_1777_ = v___y_1795_;
v___y_1778_ = v___y_1792_;
v___y_1779_ = v___y_1794_;
v___y_1780_ = v___y_1793_;
v___y_1781_ = v___x_1797_;
v_a_1782_ = v___x_1799_;
goto v___jp_1776_;
}
else
{
lean_dec_ref(v___x_1797_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_1804_;
}
}
}
v___jp_1805_:
{
if (v_a_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1813_ = lean_box(v_tmp_1568_);
v___x_1814_ = lean_obj_tag_nat(v___x_1813_);
lean_dec(v___x_1813_);
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = lean_nat_dec_eq(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1808_);
v___x_1818_ = l_IO_FS_writeFile(v___y_1807_, v___x_1817_);
lean_dec_ref(v___x_1817_);
lean_dec_ref(v___y_1807_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_dec_ref_known(v___x_1818_, 1);
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1810_;
v___y_1795_ = v___y_1809_;
goto v___jp_1791_;
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1823_ = lean_io_error_to_string(v_a_1819_);
v___x_1824_ = 3;
v___x_1825_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*1, v___x_1824_);
lean_inc_ref(v___y_1809_);
v___x_1826_ = lean_apply_2(v___y_1809_, v___x_1825_, lean_box(0));
v___x_1827_ = lean_box(0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1827_);
v___x_1829_ = v___x_1821_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec(v___y_1808_);
v___x_1832_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1833_ = l_IO_FS_writeFile(v___y_1807_, v___x_1832_);
lean_dec_ref(v___y_1807_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_dec_ref_known(v___x_1833_, 1);
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1810_;
v___y_1795_ = v___y_1809_;
goto v___jp_1791_;
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1846_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1846_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1838_ = lean_io_error_to_string(v_a_1834_);
v___x_1839_ = 3;
v___x_1840_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*1, v___x_1839_);
lean_inc_ref(v___y_1809_);
v___x_1841_ = lean_apply_2(v___y_1809_, v___x_1840_, lean_box(0));
v___x_1842_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1842_);
v___x_1844_ = v___x_1836_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1810_;
v___y_1795_ = v___y_1809_;
goto v___jp_1791_;
}
}
v___jp_1847_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; uint8_t v___x_1857_; 
v___x_1853_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1566_);
v___x_1854_ = l_Lake_joinRelative(v_dir_1566_, v___x_1853_);
v___x_1855_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1856_ = l_System_FilePath_pathExists(v___x_1854_);
v___x_1857_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1857_ == 0)
{
v___y_1806_ = v___y_1848_;
v___y_1807_ = v___x_1854_;
v___y_1808_ = v___y_1849_;
v___y_1809_ = v___y_1850_;
v___y_1810_ = v___y_1852_;
v___y_1811_ = v___y_1851_;
v_a_1812_ = v___x_1856_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = ((size_t)0ULL);
v___x_1860_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1855_, v___x_1859_, v___x_1860_, v___x_1858_, v___y_1850_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
v___y_1806_ = v___y_1848_;
v___y_1807_ = v___x_1854_;
v___y_1808_ = v___y_1849_;
v___y_1809_ = v___y_1850_;
v___y_1810_ = v___y_1852_;
v___y_1811_ = v___y_1851_;
v_a_1812_ = v___x_1856_;
goto v___jp_1805_;
}
else
{
lean_dec_ref(v___x_1854_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_1861_;
}
}
}
v___jp_1862_:
{
switch(v_tmp_1568_)
{
case 0:
{
v___y_1848_ = v___y_1863_;
v___y_1849_ = v___y_1864_;
v___y_1850_ = v___y_1867_;
v___y_1851_ = v___y_1866_;
v___y_1852_ = v___y_1865_;
goto v___jp_1847_;
}
case 1:
{
v___y_1848_ = v___y_1863_;
v___y_1849_ = v___y_1864_;
v___y_1850_ = v___y_1867_;
v___y_1851_ = v___y_1866_;
v___y_1852_ = v___y_1865_;
goto v___jp_1847_;
}
default: 
{
lean_dec(v___y_1864_);
v___y_1792_ = v___y_1863_;
v___y_1793_ = v___y_1866_;
v___y_1794_ = v___y_1865_;
v___y_1795_ = v___y_1867_;
goto v___jp_1791_;
}
}
}
v___jp_1868_:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_IO_FS_writeFile(v___y_1872_, v___y_1875_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___y_1872_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_dec_ref_known(v___x_1876_, 1);
v___y_1863_ = v___y_1870_;
v___y_1864_ = v___y_1871_;
v___y_1865_ = v___y_1874_;
v___y_1866_ = v___y_1873_;
v___y_1867_ = v___y_1869_;
goto v___jp_1862_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1889_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1889_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1881_ = lean_io_error_to_string(v_a_1877_);
v___x_1882_ = 3;
v___x_1883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*1, v___x_1882_);
lean_inc_ref(v___y_1869_);
v___x_1884_ = lean_apply_2(v___y_1869_, v___x_1883_, lean_box(0));
v___x_1885_ = lean_box(0);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1885_);
v___x_1887_ = v___x_1879_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
v___jp_1890_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1897_ = lean_box(v_tmp_1568_);
v___x_1898_ = lean_obj_tag_nat(v___x_1897_);
lean_dec(v___x_1897_);
v___x_1899_ = lean_unsigned_to_nat(4u);
v___x_1900_ = lean_nat_dec_eq(v___x_1898_, v___x_1899_);
if (v___x_1900_ == 0)
{
uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = 1;
lean_inc_n(v___y_1892_, 2);
v___x_1902_ = l_Lean_Name_toString(v___y_1892_, v___x_1901_);
v___x_1903_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1902_, v___y_1892_);
lean_dec_ref(v___x_1902_);
v___y_1869_ = v___y_1896_;
v___y_1870_ = v___y_1891_;
v___y_1871_ = v___y_1892_;
v___y_1872_ = v___y_1893_;
v___y_1873_ = v___y_1895_;
v___y_1874_ = v___y_1894_;
v___y_1875_ = v___x_1903_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1904_; 
lean_inc(v___y_1892_);
v___x_1904_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1892_);
v___y_1869_ = v___y_1896_;
v___y_1870_ = v___y_1891_;
v___y_1871_ = v___y_1892_;
v___y_1872_ = v___y_1893_;
v___y_1873_ = v___y_1895_;
v___y_1874_ = v___y_1894_;
v___y_1875_ = v___x_1904_;
goto v___jp_1868_;
}
}
v___jp_1905_:
{
if (v_a_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = l_IO_FS_createDirAll(v___y_1906_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref_known(v___x_1914_, 1);
v___x_1915_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1916_ = l_IO_FS_writeFile(v___y_1912_, v___x_1915_);
lean_dec_ref(v___y_1912_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_dec_ref_known(v___x_1916_, 1);
v___y_1891_ = v___y_1907_;
v___y_1892_ = v___y_1908_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v___y_1911_;
v___y_1895_ = v___y_1910_;
v___y_1896_ = v_a_1565_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1921_ = lean_io_error_to_string(v_a_1917_);
v___x_1922_ = 3;
v___x_1923_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*1, v___x_1922_);
lean_inc_ref(v_a_1565_);
v___x_1924_ = lean_apply_2(v_a_1565_, v___x_1923_, lean_box(0));
v___x_1925_ = lean_box(0);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1925_);
v___x_1927_ = v___x_1919_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1930_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1932_ = v___x_1914_;
v_isShared_1933_ = v_isSharedCheck_1942_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1914_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1942_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1934_ = lean_io_error_to_string(v_a_1930_);
v___x_1935_ = 3;
v___x_1936_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set_uint8(v___x_1936_, sizeof(void*)*1, v___x_1935_);
lean_inc_ref(v_a_1565_);
v___x_1937_ = lean_apply_2(v_a_1565_, v___x_1936_, lean_box(0));
v___x_1938_ = lean_box(0);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1938_);
v___x_1940_ = v___x_1932_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_dec_ref(v___y_1912_);
lean_dec_ref(v___y_1906_);
v___y_1891_ = v___y_1907_;
v___y_1892_ = v___y_1908_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v___y_1911_;
v___y_1895_ = v___y_1910_;
v___y_1896_ = v_a_1565_;
goto v___jp_1890_;
}
}
v___jp_1946_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_inc(v___y_1951_);
lean_inc(v___y_1948_);
lean_inc(v_name_1567_);
v___x_1952_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1568_, v_lang_1569_, v_name_1567_, v___y_1948_, v___y_1951_);
v___x_1953_ = l_IO_FS_writeFile(v_configFile_1945_, v___x_1952_);
lean_dec_ref(v___x_1952_);
lean_dec_ref(v_configFile_1945_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_dec_ref_known(v___x_1953_, 1);
if (lean_obj_tag(v___y_1949_) == 1)
{
lean_object* v_val_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; 
v_val_1954_ = lean_ctor_get(v___y_1949_, 0);
lean_inc_n(v_val_1954_, 2);
lean_dec_ref_known(v___y_1949_, 1);
v___x_1955_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1956_ = l_System_FilePath_withExtension(v_val_1954_, v___x_1955_);
v___x_1957_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v___x_1956_);
v___x_1958_ = l_Lake_joinRelative(v___x_1956_, v___x_1957_);
v___x_1959_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1960_ = l_System_FilePath_pathExists(v___x_1958_);
v___x_1961_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1961_ == 0)
{
v___y_1906_ = v___x_1956_;
v___y_1907_ = v___y_1947_;
v___y_1908_ = v___y_1948_;
v___y_1909_ = v_val_1954_;
v___y_1910_ = v___y_1951_;
v___y_1911_ = v___y_1950_;
v___y_1912_ = v___x_1958_;
v_a_1913_ = v___x_1960_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1962_; size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1962_ = lean_box(0);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1959_, v___x_1963_, v___x_1964_, v___x_1962_, v_a_1565_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref_known(v___x_1965_, 1);
v___y_1906_ = v___x_1956_;
v___y_1907_ = v___y_1947_;
v___y_1908_ = v___y_1948_;
v___y_1909_ = v_val_1954_;
v___y_1910_ = v___y_1951_;
v___y_1911_ = v___y_1950_;
v___y_1912_ = v___x_1958_;
v_a_1913_ = v___x_1960_;
goto v___jp_1905_;
}
else
{
lean_dec_ref(v___x_1958_);
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1954_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_1965_;
}
}
}
else
{
lean_dec(v___y_1949_);
v___y_1863_ = v___y_1947_;
v___y_1864_ = v___y_1948_;
v___y_1865_ = v___y_1950_;
v___y_1866_ = v___y_1951_;
v___y_1867_ = v_a_1565_;
goto v___jp_1862_;
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1966_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1968_ = v___x_1953_;
v_isShared_1969_ = v_isSharedCheck_1978_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1953_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1978_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1970_ = lean_io_error_to_string(v_a_1966_);
v___x_1971_ = 3;
v___x_1972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1972_, 0, v___x_1970_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*1, v___x_1971_);
lean_inc_ref(v_a_1565_);
v___x_1973_ = lean_apply_2(v_a_1565_, v___x_1972_, lean_box(0));
v___x_1974_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1974_);
v___x_1976_ = v___x_1968_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
v___jp_1979_:
{
lean_object* v_lean_1982_; lean_object* v_toolchain_1983_; lean_object* v___x_1984_; 
v_lean_1982_ = lean_ctor_get(v_env_1570_, 1);
v_toolchain_1983_ = lean_ctor_get(v_env_1570_, 19);
lean_inc_ref(v_toolchain_1983_);
v___x_1984_ = l_Lake_ToolchainVer_ofString(v_toolchain_1983_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_ver_1985_; lean_object* v___x_1986_; 
v_ver_1985_ = lean_ctor_get(v___x_1984_, 1);
lean_inc_ref(v_ver_1985_);
lean_dec_ref_known(v___x_1984_, 2);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_ver_1985_);
lean_inc_ref(v_toolchain_1983_);
lean_inc_ref(v_lean_1982_);
v___y_1947_ = v_lean_1982_;
v___y_1948_ = v_fst_1980_;
v___y_1949_ = v_snd_1981_;
v___y_1950_ = v_toolchain_1983_;
v___y_1951_ = v___x_1986_;
goto v___jp_1946_;
}
else
{
lean_object* v___x_1987_; 
lean_dec_ref(v___x_1984_);
v___x_1987_ = lean_box(0);
lean_inc_ref(v_toolchain_1983_);
lean_inc_ref(v_lean_1982_);
v___y_1947_ = v_lean_1982_;
v___y_1948_ = v_fst_1980_;
v___y_1949_ = v_snd_1981_;
v___y_1950_ = v_toolchain_1983_;
v___y_1951_ = v___x_1987_;
goto v___jp_1946_;
}
}
v___jp_1988_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_box(0);
lean_inc(v_name_1567_);
v_fst_1980_ = v_name_1567_;
v_snd_1981_ = v___x_1989_;
goto v___jp_1979_;
}
v___jp_1990_:
{
if (v_a_1993_ == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___y_1992_);
v_fst_1980_ = v___y_1991_;
v_snd_1981_ = v___x_1994_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_1995_; 
lean_dec_ref(v___y_1992_);
v___x_1995_ = lean_box(0);
v_fst_1980_ = v___y_1991_;
v_snd_1981_ = v___x_1995_;
goto v___jp_1979_;
}
}
v___jp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_1999_ = lean_box(v_tmp_1568_);
v___x_2000_ = lean_obj_tag_nat(v___x_1999_);
lean_dec(v___x_1999_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_dec_eq(v___x_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
if (v_a_1998_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; uint8_t v___x_2007_; 
lean_inc(v_name_1567_);
v___x_2003_ = l_Lake_toUpperCamelCase(v_name_1567_);
lean_inc(v___x_2003_);
v___x_2004_ = l_Lean_modToFilePath(v_dir_1566_, v___x_2003_, v___y_1997_);
v___x_2005_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2006_ = l_System_FilePath_pathExists(v___x_2004_);
v___x_2007_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2007_ == 0)
{
v___y_1991_ = v___x_2003_;
v___y_1992_ = v___x_2004_;
v_a_1993_ = v___x_2006_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2005_, v___x_2009_, v___x_2010_, v___x_2008_, v_a_1565_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
v___y_1991_ = v___x_2003_;
v___y_1992_ = v___x_2004_;
v_a_1993_ = v___x_2006_;
goto v___jp_1990_;
}
else
{
lean_dec_ref(v___x_2004_);
lean_dec(v___x_2003_);
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_2011_;
}
}
}
else
{
goto v___jp_1988_;
}
}
else
{
goto v___jp_1988_;
}
}
v___jp_2012_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2013_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc(v_name_1567_);
v___x_2014_ = l_Lean_modToFilePath(v_dir_1566_, v_name_1567_, v___x_2013_);
v___x_2015_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2016_ = l_System_FilePath_pathExists(v___x_2014_);
lean_dec_ref(v___x_2014_);
v___x_2017_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2017_ == 0)
{
v___y_1997_ = v___x_2013_;
v_a_1998_ = v___x_2016_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2015_, v___x_2019_, v___x_2020_, v___x_2018_, v_a_1565_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_dec_ref_known(v___x_2021_, 1);
v___y_1997_ = v___x_2013_;
v_a_1998_ = v___x_2016_;
goto v___jp_1996_;
}
else
{
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_2021_;
}
}
}
v___jp_2022_:
{
if (lean_obj_tag(v___y_2023_) == 0)
{
lean_dec_ref_known(v___y_2023_, 1);
goto v___jp_2012_;
}
else
{
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___y_2023_;
}
}
v___jp_2024_:
{
if (v_a_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = lean_unsigned_to_nat(0u);
v___x_2027_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1566_);
v___x_2028_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1566_, v_tmp_1568_, v___x_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 2);
v___x_2030_ = lean_array_get_size(v_a_2029_);
v___x_2031_ = lean_nat_dec_lt(v___x_2026_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_dec(v_a_2029_);
goto v___jp_2012_;
}
else
{
lean_object* v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = ((size_t)0ULL);
v___x_2034_ = lean_usize_of_nat(v___x_2030_);
v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2029_, v___x_2033_, v___x_2034_, v___x_2032_, v_a_1565_);
lean_dec(v_a_2029_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_dec_ref_known(v___x_2035_, 1);
goto v___jp_2012_;
}
else
{
v___y_2023_ = v___x_2035_;
goto v___jp_2022_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v_a_2036_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2028_, 2);
v___x_2037_ = lean_array_get_size(v_a_2036_);
v___x_2038_ = lean_nat_dec_lt(v___x_2026_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec(v_a_2036_);
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = lean_usize_of_nat(v___x_2037_);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2036_, v___x_2042_, v___x_2043_, v___x_2041_, v_a_1565_);
lean_dec(v_a_2036_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2052_);
v___x_2046_ = v___x_2044_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2041_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
v___y_2023_ = v___x_2044_;
goto v___jp_2022_;
}
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec_ref(v_configFile_1945_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v___x_2053_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17));
lean_inc_ref(v_a_1565_);
v___x_2054_ = lean_apply_2(v_a_1565_, v___x_2053_, lean_box(0));
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2064_, lean_object* v_dir_2065_, lean_object* v_name_2066_, lean_object* v_tmp_2067_, lean_object* v_lang_2068_, lean_object* v_env_2069_, lean_object* v_offline_2070_, lean_object* v_a_2071_){
_start:
{
uint8_t v_tmp_boxed_2072_; uint8_t v_lang_boxed_2073_; uint8_t v_offline_boxed_2074_; lean_object* v_res_2075_; 
v_tmp_boxed_2072_ = lean_unbox(v_tmp_2067_);
v_lang_boxed_2073_ = lean_unbox(v_lang_2068_);
v_offline_boxed_2074_ = lean_unbox(v_offline_2070_);
v_res_2075_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2064_, v_dir_2065_, v_name_2066_, v_tmp_boxed_2072_, v_lang_boxed_2073_, v_env_2069_, v_offline_boxed_2074_);
lean_dec_ref(v_a_2064_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* v_name_2077_, uint8_t v_tmp_2078_, uint8_t v_lang_2079_, lean_object* v_env_2080_, lean_object* v_cwd_2081_, uint8_t v_offline_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v___y_2086_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v_a_2107_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2143_ = lean_string_dec_eq(v_name_2077_, v___x_2142_);
if (v___x_2143_ == 0)
{
v_a_2107_ = v_name_2077_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2144_; 
lean_dec_ref(v_name_2077_);
lean_inc_ref(v_cwd_2081_);
v___x_2144_ = lean_io_realpath(v_cwd_2081_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2162_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2162_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2162_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; 
lean_inc(v_a_2145_);
v___x_2149_ = l_System_FilePath_fileName(v_a_2145_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec_ref(v_cwd_2081_);
lean_dec_ref(v_env_2080_);
v___x_2150_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2151_ = lean_string_append(v___x_2150_, v_a_2145_);
lean_dec(v_a_2145_);
v___x_2152_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
v___x_2154_ = 3;
v___x_2155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*1, v___x_2154_);
lean_inc_ref(v_a_2083_);
v___x_2156_ = lean_apply_2(v_a_2083_, v___x_2155_, lean_box(0));
v___x_2157_ = lean_box(0);
if (v_isShared_2148_ == 0)
{
lean_ctor_set_tag(v___x_2147_, 1);
lean_ctor_set(v___x_2147_, 0, v___x_2157_);
v___x_2159_ = v___x_2147_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
else
{
lean_object* v_val_2161_; 
lean_del_object(v___x_2147_);
lean_dec(v_a_2145_);
v_val_2161_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v___x_2149_, 1);
v_a_2107_ = v_val_2161_;
goto v___jp_2106_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v_cwd_2081_);
lean_dec_ref(v_env_2080_);
v_a_2163_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2165_ = v___x_2144_;
v_isShared_2166_ = v_isSharedCheck_2175_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2144_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2175_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2167_ = lean_io_error_to_string(v_a_2163_);
v___x_2168_ = 3;
v___x_2169_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*1, v___x_2168_);
lean_inc_ref(v_a_2083_);
v___x_2170_ = lean_apply_2(v_a_2083_, v___x_2169_, lean_box(0));
v___x_2171_ = lean_box(0);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2171_);
v___x_2173_ = v___x_2165_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
v___jp_2085_:
{
lean_object* v___x_2087_; 
lean_inc_ref(v_cwd_2081_);
v___x_2087_ = l_IO_FS_createDirAll(v_cwd_2081_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2088_ = l_Lake_stringToLegalOrSimpleName(v___y_2086_);
v___x_2089_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2083_, v_cwd_2081_, v___x_2088_, v_tmp_2078_, v_lang_2079_, v_env_2080_, v_offline_2082_);
return v___x_2089_;
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v___y_2086_);
lean_dec_ref(v_cwd_2081_);
lean_dec_ref(v_env_2080_);
v_a_2090_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2092_ = v___x_2087_;
v_isShared_2093_ = v_isSharedCheck_2102_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2087_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2102_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2094_ = lean_io_error_to_string(v_a_2090_);
v___x_2095_ = 3;
v___x_2096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*1, v___x_2095_);
lean_inc_ref(v_a_2083_);
v___x_2097_ = lean_apply_2(v_a_2083_, v___x_2096_, lean_box(0));
v___x_2098_ = lean_box(0);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2098_);
v___x_2100_ = v___x_2092_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
v___jp_2103_:
{
if (lean_obj_tag(v___y_2105_) == 0)
{
lean_dec_ref_known(v___y_2105_, 1);
v___y_2086_ = v___y_2104_;
goto v___jp_2085_;
}
else
{
lean_dec_ref(v___y_2104_);
lean_dec_ref(v_cwd_2081_);
lean_dec_ref(v_env_2080_);
return v___y_2105_;
}
}
v___jp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_str_2112_; lean_object* v_startInclusive_2113_; lean_object* v_endExclusive_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_string_utf8_byte_size(v_a_2107_);
v___x_2110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2110_, 0, v_a_2107_);
lean_ctor_set(v___x_2110_, 1, v___x_2108_);
lean_ctor_set(v___x_2110_, 2, v___x_2109_);
v___x_2111_ = l_String_Slice_trimAscii(v___x_2110_);
v_str_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_str_2112_);
v_startInclusive_2113_ = lean_ctor_get(v___x_2111_, 1);
lean_inc(v_startInclusive_2113_);
v_endExclusive_2114_ = lean_ctor_get(v___x_2111_, 2);
lean_inc(v_endExclusive_2114_);
lean_dec_ref(v___x_2111_);
v___x_2115_ = lean_string_utf8_extract_fast(v_str_2112_, v_startInclusive_2113_, v_endExclusive_2114_);
lean_dec(v_endExclusive_2114_);
lean_dec(v_startInclusive_2113_);
lean_dec_ref(v_str_2112_);
v___x_2116_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2115_);
v___x_2117_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2115_, v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 2);
v___x_2119_ = lean_array_get_size(v_a_2118_);
v___x_2120_ = lean_nat_dec_lt(v___x_2108_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_dec(v_a_2118_);
v___y_2086_ = v___x_2115_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2121_; size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2119_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2118_, v___x_2122_, v___x_2123_, v___x_2121_, v_a_2083_);
lean_dec(v_a_2118_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_dec_ref_known(v___x_2124_, 1);
v___y_2086_ = v___x_2115_;
goto v___jp_2085_;
}
else
{
v___y_2104_ = v___x_2115_;
v___y_2105_ = v___x_2124_;
goto v___jp_2103_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_a_2125_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2117_, 2);
v___x_2126_ = lean_array_get_size(v_a_2125_);
v___x_2127_ = lean_nat_dec_lt(v___x_2108_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec(v_a_2125_);
lean_dec_ref(v___x_2115_);
lean_dec_ref(v_cwd_2081_);
lean_dec_ref(v_env_2080_);
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_box(0);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = lean_usize_of_nat(v___x_2126_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2125_, v___x_2131_, v___x_2132_, v___x_2130_, v_a_2083_);
lean_dec(v_a_2125_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v_cwd_2081_);
lean_dec_ref(v_env_2080_);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v___x_2133_, 0);
lean_dec(v_unused_2141_);
v___x_2135_ = v___x_2133_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v___x_2133_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2130_);
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2130_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
else
{
v___y_2104_ = v___x_2115_;
v___y_2105_ = v___x_2133_;
goto v___jp_2103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2176_, lean_object* v_tmp_2177_, lean_object* v_lang_2178_, lean_object* v_env_2179_, lean_object* v_cwd_2180_, lean_object* v_offline_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v_tmp_boxed_2184_; uint8_t v_lang_boxed_2185_; uint8_t v_offline_boxed_2186_; lean_object* v_res_2187_; 
v_tmp_boxed_2184_ = lean_unbox(v_tmp_2177_);
v_lang_boxed_2185_ = lean_unbox(v_lang_2178_);
v_offline_boxed_2186_ = lean_unbox(v_offline_2181_);
v_res_2187_ = l_Lake_init(v_name_2176_, v_tmp_boxed_2184_, v_lang_boxed_2185_, v_env_2179_, v_cwd_2180_, v_offline_boxed_2186_, v_a_2182_);
lean_dec_ref(v_a_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* v_name_2188_, uint8_t v_tmp_2189_, uint8_t v_lang_2190_, lean_object* v_env_2191_, lean_object* v_cwd_2192_, uint8_t v_offline_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_str_2200_; lean_object* v_startInclusive_2201_; lean_object* v_endExclusive_2202_; lean_object* v_name_2203_; lean_object* v___y_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_string_utf8_byte_size(v_name_2188_);
v___x_2198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2198_, 0, v_name_2188_);
lean_ctor_set(v___x_2198_, 1, v___x_2196_);
lean_ctor_set(v___x_2198_, 2, v___x_2197_);
v___x_2199_ = l_String_Slice_trimAscii(v___x_2198_);
v_str_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc_ref(v_str_2200_);
v_startInclusive_2201_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_startInclusive_2201_);
v_endExclusive_2202_ = lean_ctor_get(v___x_2199_, 2);
lean_inc(v_endExclusive_2202_);
lean_dec_ref(v___x_2199_);
v_name_2203_ = lean_string_utf8_extract_fast(v_str_2200_, v_startInclusive_2201_, v_endExclusive_2202_);
lean_dec(v_endExclusive_2202_);
lean_dec(v_startInclusive_2201_);
lean_dec_ref(v_str_2200_);
v___x_2225_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2203_);
v___x_2226_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2203_, v___x_2225_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 1);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 2);
v___x_2228_ = lean_array_get_size(v_a_2227_);
v___x_2229_ = lean_nat_dec_lt(v___x_2196_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_dec(v_a_2227_);
goto v___jp_2204_;
}
else
{
lean_object* v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2230_ = lean_box(0);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2228_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2227_, v___x_2231_, v___x_2232_, v___x_2230_, v_a_2194_);
lean_dec(v_a_2227_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_dec_ref_known(v___x_2233_, 1);
goto v___jp_2204_;
}
else
{
v___y_2224_ = v___x_2233_;
goto v___jp_2223_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v_a_2234_ = lean_ctor_get(v___x_2226_, 1);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2226_, 2);
v___x_2235_ = lean_array_get_size(v_a_2234_);
v___x_2236_ = lean_nat_dec_lt(v___x_2196_, v___x_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_a_2234_);
lean_dec_ref(v_name_2203_);
lean_dec_ref(v_cwd_2192_);
lean_dec_ref(v_env_2191_);
v___x_2237_ = lean_box(0);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; size_t v___x_2240_; size_t v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = lean_box(0);
v___x_2240_ = ((size_t)0ULL);
v___x_2241_ = lean_usize_of_nat(v___x_2235_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2234_, v___x_2240_, v___x_2241_, v___x_2239_, v_a_2194_);
lean_dec(v_a_2234_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec_ref(v_name_2203_);
lean_dec_ref(v_cwd_2192_);
lean_dec_ref(v_env_2191_);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2242_, 0);
lean_dec(v_unused_2250_);
v___x_2244_ = v___x_2242_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_dec(v___x_2242_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 1);
lean_ctor_set(v___x_2244_, 0, v___x_2239_);
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2239_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
v___y_2224_ = v___x_2242_;
goto v___jp_2223_;
}
}
}
v___jp_2204_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lake_stringToLegalOrSimpleName(v_name_2203_);
lean_inc(v___x_2205_);
v___x_2206_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2205_);
v___x_2207_ = l_Lake_joinRelative(v_cwd_2192_, v___x_2206_);
lean_inc_ref(v___x_2207_);
v___x_2208_ = l_IO_FS_createDirAll(v___x_2207_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref_known(v___x_2208_, 1);
v___x_2209_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2194_, v___x_2207_, v___x_2205_, v_tmp_2189_, v_lang_2190_, v_env_2191_, v_offline_2193_);
return v___x_2209_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v___x_2207_);
lean_dec(v___x_2205_);
lean_dec_ref(v_env_2191_);
v_a_2210_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2212_ = v___x_2208_;
v_isShared_2213_ = v_isSharedCheck_2222_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2208_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2222_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2214_ = lean_io_error_to_string(v_a_2210_);
v___x_2215_ = 3;
v___x_2216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*1, v___x_2215_);
lean_inc_ref(v_a_2194_);
v___x_2217_ = lean_apply_2(v_a_2194_, v___x_2216_, lean_box(0));
v___x_2218_ = lean_box(0);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2218_);
v___x_2220_ = v___x_2212_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
v___jp_2223_:
{
if (lean_obj_tag(v___y_2224_) == 0)
{
lean_dec_ref_known(v___y_2224_, 1);
goto v___jp_2204_;
}
else
{
lean_dec_ref(v_name_2203_);
lean_dec_ref(v_cwd_2192_);
lean_dec_ref(v_env_2191_);
return v___y_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2251_, lean_object* v_tmp_2252_, lean_object* v_lang_2253_, lean_object* v_env_2254_, lean_object* v_cwd_2255_, lean_object* v_offline_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
uint8_t v_tmp_boxed_2259_; uint8_t v_lang_boxed_2260_; uint8_t v_offline_boxed_2261_; lean_object* v_res_2262_; 
v_tmp_boxed_2259_ = lean_unbox(v_tmp_2252_);
v_lang_boxed_2260_ = lean_unbox(v_lang_2253_);
v_offline_boxed_2261_ = lean_unbox(v_offline_2256_);
v_res_2262_ = l_Lake_new(v_name_2251_, v_tmp_boxed_2259_, v_lang_boxed_2260_, v_env_2254_, v_cwd_2255_, v_offline_boxed_2261_, v_a_2257_);
lean_dec_ref(v_a_2257_);
return v_res_2262_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents);
l___private_Lake_CLI_Init_0__Lake_mainFileName = _init_l___private_Lake_CLI_Init_0__Lake_mainFileName();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName);
l_Lake_instInhabitedInitTemplate = _init_l_Lake_instInhabitedInitTemplate();
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__0___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___redArg___closed__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Init(builtin);
}
#ifdef __cplusplus
}
#endif
