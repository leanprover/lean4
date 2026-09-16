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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 201, .m_capacity = 201, .m_length = 200, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 488, .m_capacity = 488, .m_length = 487, .m_data = "name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\n# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages\npermissions:\n  contents: read # Read access to repository contents\n  pages: write # Write access to GitHub Pages\n  id-token: write # Write access to ID tokens\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n      - uses: leanprover-community/docgen-action@v1\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1951, .m_capacity = 1951, .m_length = 1950, .m_data = "name: Update Dependencies\n\non:\n  # schedule:             # Sets a schedule to trigger the workflow\n  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)\n  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface\n\njobs:\n  check-for-updates: # Determines which updates to apply.\n    runs-on: ubuntu-latest\n    outputs:\n      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}\n      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}\n    steps:\n      - name: Run the action\n        id: check-for-updates\n        uses: leanprover-community/mathlib-update-action@v1\n        # START CONFIGURATION BLOCK 1\n        # END CONFIGURATION BLOCK 1\n  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write      # Grants permission to push changes to the repository\n      issues: write        # Grants permission to create or update issues\n      pull-requests: write # Grants permission to create or update pull requests\n    needs: check-for-updates\n    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}\n    strategy: # Runs for each update discovered by the `check-for-updates` job.\n      max-parallel: 1 # Ensures that the PRs/issues are created in order.\n      matrix:\n        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}\n    steps:\n      - name: Run the action\n        id: update-the-repo\n        uses: leanprover-community/mathlib-update-action/do-update@v1\n        with:\n          tag: ${{ matrix.tag }}\n          # START CONFIGURATION BLOCK 2\n          on_update_succeeds: pr # Create a pull request if the update succeeds\n          on_update_fails: issue # Create an issue if the update fails\n          # END CONFIGURATION BLOCK 2\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 428, .m_capacity = 428, .m_length = 427, .m_data = "name: Create Release\n\non:\n  push:\n    branches:\n      - 'main'\n      - 'master'\n    paths:\n      - 'lean-toolchain'\n\njobs:\n  lean-release-tag:\n    name: Add Lean release tag\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n    - name: lean-release-tag action\n      uses: leanprover-community/lean-release-tag@v1\n      with:\n        do-release: true\n        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "update.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "create-release.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created Mathlib update CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created create-release CI workflow at '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "create-release CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Mathlib update CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "lean-action CI workflow already exists"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__17 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__17_value;
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
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Basic.lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "package already initialized"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18_value;
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
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)}};
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t v_x_332_){
_start:
{
switch(v_x_332_)
{
case 0:
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(0u);
return v___x_333_;
}
case 1:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(1u);
return v___x_334_;
}
case 2:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(2u);
return v___x_335_;
}
case 3:
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(3u);
return v___x_336_;
}
default: 
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(4u);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object* v_x_338_){
_start:
{
uint8_t v_x_boxed_339_; lean_object* v_res_340_; 
v_x_boxed_339_ = lean_unbox(v_x_338_);
v_res_340_ = l_Lake_InitTemplate_ctorIdx(v_x_boxed_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* v_k_341_){
_start:
{
lean_inc(v_k_341_);
return v_k_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* v_k_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lake_InitTemplate_ctorElim___redArg(v_k_342_);
lean_dec(v_k_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* v_motive_344_, lean_object* v_ctorIdx_345_, uint8_t v_t_346_, lean_object* v_h_347_, lean_object* v_k_348_){
_start:
{
lean_inc(v_k_348_);
return v_k_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* v_motive_349_, lean_object* v_ctorIdx_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_k_353_){
_start:
{
uint8_t v_t_boxed_354_; lean_object* v_res_355_; 
v_t_boxed_354_ = lean_unbox(v_t_351_);
v_res_355_ = l_Lake_InitTemplate_ctorElim(v_motive_349_, v_ctorIdx_350_, v_t_boxed_354_, v_h_352_, v_k_353_);
lean_dec(v_k_353_);
lean_dec(v_ctorIdx_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* v_std_356_){
_start:
{
lean_inc(v_std_356_);
return v_std_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* v_std_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lake_InitTemplate_std_elim___redArg(v_std_357_);
lean_dec(v_std_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* v_motive_359_, uint8_t v_t_360_, lean_object* v_h_361_, lean_object* v_std_362_){
_start:
{
lean_inc(v_std_362_);
return v_std_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* v_motive_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_std_366_){
_start:
{
uint8_t v_t_boxed_367_; lean_object* v_res_368_; 
v_t_boxed_367_ = lean_unbox(v_t_364_);
v_res_368_ = l_Lake_InitTemplate_std_elim(v_motive_363_, v_t_boxed_367_, v_h_365_, v_std_366_);
lean_dec(v_std_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* v_exe_369_){
_start:
{
lean_inc(v_exe_369_);
return v_exe_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* v_exe_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_InitTemplate_exe_elim___redArg(v_exe_370_);
lean_dec(v_exe_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* v_motive_372_, uint8_t v_t_373_, lean_object* v_h_374_, lean_object* v_exe_375_){
_start:
{
lean_inc(v_exe_375_);
return v_exe_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* v_motive_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_exe_379_){
_start:
{
uint8_t v_t_boxed_380_; lean_object* v_res_381_; 
v_t_boxed_380_ = lean_unbox(v_t_377_);
v_res_381_ = l_Lake_InitTemplate_exe_elim(v_motive_376_, v_t_boxed_380_, v_h_378_, v_exe_379_);
lean_dec(v_exe_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* v_lib_382_){
_start:
{
lean_inc(v_lib_382_);
return v_lib_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* v_lib_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lake_InitTemplate_lib_elim___redArg(v_lib_383_);
lean_dec(v_lib_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* v_motive_385_, uint8_t v_t_386_, lean_object* v_h_387_, lean_object* v_lib_388_){
_start:
{
lean_inc(v_lib_388_);
return v_lib_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* v_motive_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_lib_392_){
_start:
{
uint8_t v_t_boxed_393_; lean_object* v_res_394_; 
v_t_boxed_393_ = lean_unbox(v_t_390_);
v_res_394_ = l_Lake_InitTemplate_lib_elim(v_motive_389_, v_t_boxed_393_, v_h_391_, v_lib_392_);
lean_dec(v_lib_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* v_mathLax_395_){
_start:
{
lean_inc(v_mathLax_395_);
return v_mathLax_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* v_mathLax_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lake_InitTemplate_mathLax_elim___redArg(v_mathLax_396_);
lean_dec(v_mathLax_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* v_motive_398_, uint8_t v_t_399_, lean_object* v_h_400_, lean_object* v_mathLax_401_){
_start:
{
lean_inc(v_mathLax_401_);
return v_mathLax_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_mathLax_405_){
_start:
{
uint8_t v_t_boxed_406_; lean_object* v_res_407_; 
v_t_boxed_406_ = lean_unbox(v_t_403_);
v_res_407_ = l_Lake_InitTemplate_mathLax_elim(v_motive_402_, v_t_boxed_406_, v_h_404_, v_mathLax_405_);
lean_dec(v_mathLax_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* v_math_408_){
_start:
{
lean_inc(v_math_408_);
return v_math_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* v_math_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_InitTemplate_math_elim___redArg(v_math_409_);
lean_dec(v_math_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* v_motive_411_, uint8_t v_t_412_, lean_object* v_h_413_, lean_object* v_math_414_){
_start:
{
lean_inc(v_math_414_);
return v_math_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_math_418_){
_start:
{
uint8_t v_t_boxed_419_; lean_object* v_res_420_; 
v_t_boxed_419_ = lean_unbox(v_t_416_);
v_res_420_ = l_Lake_InitTemplate_math_elim(v_motive_415_, v_t_boxed_419_, v_h_417_, v_math_418_);
lean_dec(v_math_418_);
return v_res_420_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(2u);
v___x_437_ = lean_nat_to_int(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_to_int(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t v_x_440_, lean_object* v_prec_441_){
_start:
{
lean_object* v___y_443_; lean_object* v___y_450_; lean_object* v___y_457_; lean_object* v___y_464_; lean_object* v___y_471_; 
switch(v_x_440_)
{
case 0:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(1024u);
v___x_478_ = lean_nat_dec_le(v___x_477_, v_prec_441_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_443_ = v___x_479_;
goto v___jp_442_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_443_ = v___x_480_;
goto v___jp_442_;
}
}
case 1:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1024u);
v___x_482_ = lean_nat_dec_le(v___x_481_, v_prec_441_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_450_ = v___x_483_;
goto v___jp_449_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_450_ = v___x_484_;
goto v___jp_449_;
}
}
case 2:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1024u);
v___x_486_ = lean_nat_dec_le(v___x_485_, v_prec_441_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_457_ = v___x_487_;
goto v___jp_456_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_457_ = v___x_488_;
goto v___jp_456_;
}
}
case 3:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1024u);
v___x_490_ = lean_nat_dec_le(v___x_489_, v_prec_441_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_464_ = v___x_491_;
goto v___jp_463_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_464_ = v___x_492_;
goto v___jp_463_;
}
}
default: 
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(1024u);
v___x_494_ = lean_nat_dec_le(v___x_493_, v_prec_441_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__10, &l_Lake_instReprInitTemplate_repr___closed__10_once, _init_l_Lake_instReprInitTemplate_repr___closed__10);
v___y_471_ = v___x_495_;
goto v___jp_470_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_obj_once(&l_Lake_instReprInitTemplate_repr___closed__11, &l_Lake_instReprInitTemplate_repr___closed__11_once, _init_l_Lake_instReprInitTemplate_repr___closed__11);
v___y_471_ = v___x_496_;
goto v___jp_470_;
}
}
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_444_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__1));
lean_inc(v___y_443_);
v___x_445_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_445_, 0, v___y_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = 0;
v___x_447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1, v___x_446_);
v___x_448_ = l_Repr_addAppParen(v___x_447_, v_prec_441_);
return v___x_448_;
}
v___jp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__3));
lean_inc(v___y_450_);
v___x_452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_452_, 0, v___y_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = 0;
v___x_454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1, v___x_453_);
v___x_455_ = l_Repr_addAppParen(v___x_454_, v_prec_441_);
return v___x_455_;
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__5));
lean_inc(v___y_457_);
v___x_459_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_459_, 0, v___y_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = 0;
v___x_461_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*1, v___x_460_);
v___x_462_ = l_Repr_addAppParen(v___x_461_, v_prec_441_);
return v___x_462_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_465_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__7));
lean_inc(v___y_464_);
v___x_466_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_466_, 0, v___y_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = 0;
v___x_468_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1, v___x_467_);
v___x_469_ = l_Repr_addAppParen(v___x_468_, v_prec_441_);
return v___x_469_;
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_472_ = ((lean_object*)(l_Lake_instReprInitTemplate_repr___closed__9));
lean_inc(v___y_471_);
v___x_473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_473_, 0, v___y_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = 0;
v___x_475_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1, v___x_474_);
v___x_476_ = l_Repr_addAppParen(v___x_475_, v_prec_441_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* v_x_497_, lean_object* v_prec_498_){
_start:
{
uint8_t v_x_279__boxed_499_; lean_object* v_res_500_; 
v_x_279__boxed_499_ = lean_unbox(v_x_497_);
v_res_500_ = l_Lake_instReprInitTemplate_repr(v_x_279__boxed_499_, v_prec_498_);
lean_dec(v_prec_498_);
return v_res_500_;
}
}
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object* v_n_503_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_dec_le(v_n_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(2u);
v___x_507_ = lean_nat_dec_le(v_n_503_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(3u);
v___x_509_ = lean_nat_dec_le(v_n_503_, v___x_508_);
if (v___x_509_ == 0)
{
uint8_t v___x_510_; 
v___x_510_ = 4;
return v___x_510_;
}
else
{
uint8_t v___x_511_; 
v___x_511_ = 3;
return v___x_511_;
}
}
else
{
uint8_t v___x_512_; 
v___x_512_ = 2;
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_nat_dec_le(v_n_503_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = 1;
return v___x_515_;
}
else
{
uint8_t v___x_516_; 
v___x_516_ = 0;
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* v_n_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Lake_InitTemplate_ofNat(v_n_517_);
lean_dec(v_n_517_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t v_x_520_, uint8_t v_y_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = l_Lake_InitTemplate_ctorIdx(v_x_520_);
v___x_523_ = l_Lake_InitTemplate_ctorIdx(v_y_521_);
v___x_524_ = lean_nat_dec_eq(v___x_522_, v___x_523_);
lean_dec(v___x_523_);
lean_dec(v___x_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* v_x_525_, lean_object* v_y_526_){
_start:
{
uint8_t v_x_20__boxed_527_; uint8_t v_y_21__boxed_528_; uint8_t v_res_529_; lean_object* v_r_530_; 
v_x_20__boxed_527_ = lean_unbox(v_x_525_);
v_y_21__boxed_528_ = lean_unbox(v_y_526_);
v_res_529_ = l_Lake_instDecidableEqInitTemplate(v_x_20__boxed_527_, v_y_21__boxed_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate(void){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__0));
v___x_554_ = lean_string_dec_eq(v_x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__1));
v___x_556_ = lean_string_dec_eq(v_x_552_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__2));
v___x_558_ = lean_string_dec_eq(v_x_552_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__3));
v___x_560_ = lean_string_dec_eq(v_x_552_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__4));
v___x_562_ = lean_string_dec_eq(v_x_552_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
v___x_563_ = lean_box(0);
return v___x_563_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__5));
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__6));
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__7));
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__8));
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Lake_InitTemplate_ofString_x3f___closed__9));
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lake_InitTemplate_ofString_x3f(v_x_569_);
lean_dec_ref(v_x_569_);
return v_res_570_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1(void){
_start:
{
uint32_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = l_Lean_idBeginEscape;
v___x_573_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_574_ = lean_string_push(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2(void){
_start:
{
uint32_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_idEndEscape;
v___x_576_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_577_ = lean_string_push(v___x_576_, v___x_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* v_id_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
v___x_580_ = lean_string_append(v___x_579_, v_id_578_);
v___x_581_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2, &l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* v_id_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_id_583_);
lean_dec_ref(v_id_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* v_msg_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_587_ = lean_panic_fn_borrowed(v___x_586_, v_msg_585_);
return v___x_587_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_591_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_592_ = lean_unsigned_to_nat(23u);
v___x_593_ = lean_unsigned_to_nat(350u);
v___x_594_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_595_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_596_ = l_mkPanicMessageWithDecl(v___x_595_, v___x_594_, v___x_593_, v___x_592_, v___x_591_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2));
v___x_599_ = lean_unsigned_to_nat(23u);
v___x_600_ = lean_unsigned_to_nat(353u);
v___x_601_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1));
v___x_602_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0));
v___x_603_ = l_mkPanicMessageWithDecl(v___x_602_, v___x_601_, v___x_600_, v___x_599_, v___x_598_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* v_x_604_){
_start:
{
switch(lean_obj_tag(v_x_604_))
{
case 0:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
v___x_606_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_605_);
return v___x_606_;
}
case 1:
{
lean_object* v_pre_607_; 
v_pre_607_ = lean_ctor_get(v_x_604_, 0);
if (lean_obj_tag(v_pre_607_) == 0)
{
lean_object* v_str_608_; lean_object* v___x_609_; 
v_str_608_ = lean_ctor_get(v_x_604_, 1);
v___x_609_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_608_);
return v___x_609_;
}
else
{
lean_object* v_str_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_str_610_ = lean_ctor_get(v_x_604_, 1);
v___x_611_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_pre_607_);
v___x_612_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_613_ = lean_string_append(v___x_611_, v___x_612_);
v___x_614_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_610_);
v___x_615_ = lean_string_append(v___x_613_, v___x_614_);
lean_dec_ref(v___x_614_);
return v___x_615_;
}
}
default: 
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5, &l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once, _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
v___x_617_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(v___x_616_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_x_618_);
lean_dec(v_x_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* v_s_620_, lean_object* v_p_621_){
_start:
{
uint32_t v___y_623_; lean_object* v___x_628_; uint8_t v_decide_629_; 
v___x_628_ = lean_string_utf8_byte_size(v_s_620_);
v_decide_629_ = lean_nat_dec_eq(v_p_621_, v___x_628_);
if (v_decide_629_ == 0)
{
uint32_t v___x_630_; uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_630_ = lean_string_utf8_get_fast(v_s_620_, v_p_621_);
v___x_631_ = 46;
v___x_632_ = lean_uint32_dec_eq(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
v___y_623_ = v___x_630_;
goto v___jp_622_;
}
else
{
uint32_t v___x_633_; 
v___x_633_ = 45;
v___y_623_ = v___x_633_;
goto v___jp_622_;
}
}
else
{
lean_dec(v_p_621_);
return v_s_620_;
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_inc(v_p_621_);
v___x_624_ = lean_string_utf8_set(v_s_620_, v_p_621_, v___y_623_);
v___x_625_ = l_Char_utf8Size(v___y_623_);
v___x_626_ = lean_nat_add(v_p_621_, v___x_625_);
lean_dec(v___x_625_);
lean_dec(v_p_621_);
v_s_620_ = v___x_624_;
v_p_621_ = v___x_626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* v_name_634_){
_start:
{
uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = 0;
v___x_636_ = l_Lean_Name_toString(v_name_634_, v___x_635_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(v___x_636_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* v_s_639_, lean_object* v_p_640_){
_start:
{
uint32_t v___y_642_; lean_object* v___x_647_; uint8_t v_decide_648_; 
v___x_647_ = lean_string_utf8_byte_size(v_s_639_);
v_decide_648_ = lean_nat_dec_eq(v_p_640_, v___x_647_);
if (v_decide_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___y_651_; uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_649_ = lean_string_utf8_get_fast(v_s_639_, v_p_640_);
v___x_654_ = 65;
v___x_655_ = lean_uint32_dec_le(v___x_654_, v___x_649_);
if (v___x_655_ == 0)
{
v___y_651_ = v___x_655_;
goto v___jp_650_;
}
else
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 90;
v___x_657_ = lean_uint32_dec_le(v___x_649_, v___x_656_);
v___y_651_ = v___x_657_;
goto v___jp_650_;
}
v___jp_650_:
{
if (v___y_651_ == 0)
{
v___y_642_ = v___x_649_;
goto v___jp_641_;
}
else
{
uint32_t v___x_652_; uint32_t v___x_653_; 
v___x_652_ = 32;
v___x_653_ = lean_uint32_add(v___x_649_, v___x_652_);
v___y_642_ = v___x_653_;
goto v___jp_641_;
}
}
}
else
{
lean_dec(v_p_640_);
return v_s_639_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_inc(v_p_640_);
v___x_643_ = lean_string_utf8_set(v_s_639_, v_p_640_, v___y_642_);
v___x_644_ = l_Char_utf8Size(v___y_642_);
v___x_645_ = lean_nat_add(v_p_640_, v___x_644_);
lean_dec(v___x_644_);
lean_dec(v_p_640_);
v_s_639_ = v___x_643_;
v_p_640_ = v___x_645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t v_tmp_660_, uint8_t v_lang_661_, lean_object* v_pkgName_662_, lean_object* v_root_663_, lean_object* v_leanVer_x3f_664_){
_start:
{
lean_object* v_pkgNameStr_665_; lean_object* v___y_667_; 
v_pkgNameStr_665_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_662_);
if (lean_obj_tag(v_leanVer_x3f_664_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___y_667_ = v___x_698_;
goto v___jp_666_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_val_699_ = lean_ctor_get(v_leanVer_x3f_664_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_leanVer_x3f_664_, 1);
v___x_700_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
v___x_701_ = l_Lake_StdVer_toString(v_val_699_);
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
lean_dec_ref(v___x_701_);
v___y_667_ = v___x_702_;
goto v___jp_666_;
}
v___jp_666_:
{
switch(v_tmp_660_)
{
case 0:
{
lean_dec_ref(v___y_667_);
if (v_lang_661_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_663_);
lean_dec(v_root_663_);
v___x_669_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_665_);
v___x_670_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_665_, v___x_669_);
v___x_671_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgNameStr_665_, v___x_668_, v___x_670_);
lean_dec_ref(v___x_668_);
return v___x_671_;
}
else
{
uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_672_ = 1;
v___x_673_ = l_Lean_Name_toString(v_root_663_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_665_);
v___x_675_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_665_, v___x_674_);
v___x_676_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(v_pkgNameStr_665_, v___x_673_, v___x_675_);
return v___x_676_;
}
}
case 1:
{
lean_dec_ref(v___y_667_);
lean_dec(v_root_663_);
if (v_lang_661_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_665_);
v___x_678_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_665_, v___x_677_);
v___x_679_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(v_pkgNameStr_665_, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_665_);
v___x_681_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_665_, v___x_680_);
v___x_682_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(v_pkgNameStr_665_, v___x_681_);
return v___x_682_;
}
}
case 2:
{
lean_dec_ref(v___y_667_);
if (v_lang_661_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_663_);
lean_dec(v_root_663_);
v___x_684_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgNameStr_665_, v___x_683_);
lean_dec_ref(v___x_683_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = 1;
v___x_686_ = l_Lean_Name_toString(v_root_663_, v___x_685_);
v___x_687_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(v_pkgNameStr_665_, v___x_686_);
return v___x_687_;
}
}
case 3:
{
if (v_lang_661_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_663_);
lean_dec(v_root_663_);
v___x_689_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgNameStr_665_, v___x_688_, v___y_667_);
lean_dec_ref(v___x_688_);
return v___x_689_;
}
else
{
uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = 1;
v___x_691_ = l_Lean_Name_toString(v_root_663_, v___x_690_);
v___x_692_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(v_pkgNameStr_665_, v___x_691_, v___y_667_);
return v___x_692_;
}
}
default: 
{
if (v_lang_661_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_663_);
lean_dec(v_root_663_);
v___x_694_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgNameStr_665_, v___x_693_, v___y_667_);
lean_dec_ref(v___x_693_);
return v___x_694_;
}
else
{
uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = 1;
v___x_696_ = l_Lean_Name_toString(v_root_663_, v___x_695_);
v___x_697_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(v_pkgNameStr_665_, v___x_696_, v___y_667_);
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* v_tmp_703_, lean_object* v_lang_704_, lean_object* v_pkgName_705_, lean_object* v_root_706_, lean_object* v_leanVer_x3f_707_){
_start:
{
uint8_t v_tmp_boxed_708_; uint8_t v_lang_boxed_709_; lean_object* v_res_710_; 
v_tmp_boxed_708_ = lean_unbox(v_tmp_703_);
v_lang_boxed_709_ = lean_unbox(v_lang_704_);
v_res_710_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_boxed_708_, v_lang_boxed_709_, v_pkgName_705_, v_root_706_, v_leanVer_x3f_707_);
return v_res_710_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7(void){
_start:
{
uint8_t v___x_720_; lean_object* v___x_721_; 
v___x_720_ = 4;
v___x_721_ = l_Lake_InitTemplate_ctorIdx(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* v_dir_738_, uint8_t v_tmp_739_, lean_object* v_a_740_){
_start:
{
uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_742_ = 0;
v___x_743_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
v___x_744_ = lean_array_push(v_a_740_, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
v___x_746_ = l_Lake_joinRelative(v_dir_738_, v___x_745_);
v___x_747_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
v___x_748_ = l_Lake_joinRelative(v___x_746_, v___x_747_);
lean_inc_ref(v___x_748_);
v___x_749_ = l_IO_FS_createDirAll(v___x_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___y_753_; uint8_t v___x_809_; 
lean_dec_ref_known(v___x_749_, 1);
v___x_750_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(v___x_748_);
v___x_751_ = l_Lake_joinRelative(v___x_748_, v___x_750_);
v___x_809_ = l_System_FilePath_pathExists(v___x_751_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = l_Lake_InitTemplate_ctorIdx(v_tmp_739_);
v___x_811_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7, &l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
v___x_812_ = lean_nat_dec_eq(v___x_810_, v___x_811_);
lean_dec(v___x_810_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
v___x_814_ = l_IO_FS_writeFile(v___x_751_, v___x_813_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref_known(v___x_814_, 1);
v___y_753_ = v___x_744_;
goto v___jp_752_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref(v___x_751_);
lean_dec_ref(v___x_748_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = lean_io_error_to_string(v_a_815_);
v___x_817_ = 3;
v___x_818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
v___x_819_ = lean_array_get_size(v___x_744_);
v___x_820_ = lean_array_push(v___x_744_, v___x_818_);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
return v___x_821_;
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
v___x_823_ = l_IO_FS_writeFile(v___x_751_, v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_dec_ref_known(v___x_823_, 1);
v___y_753_ = v___x_744_;
goto v___jp_752_;
}
else
{
lean_object* v_a_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v___x_751_);
lean_dec_ref(v___x_748_);
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = lean_io_error_to_string(v_a_824_);
v___x_826_ = 3;
v___x_827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___x_826_);
v___x_828_ = lean_array_get_size(v___x_744_);
v___x_829_ = lean_array_push(v___x_744_, v___x_827_);
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v___x_751_);
lean_dec_ref(v___x_748_);
v___x_831_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__17));
v___x_832_ = lean_array_push(v___x_744_, v___x_831_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_832_);
return v___x_834_;
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_754_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
v___x_755_ = lean_string_append(v___x_754_, v___x_751_);
lean_dec_ref(v___x_751_);
v___x_756_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_757_ = lean_string_append(v___x_755_, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*1, v___x_742_);
v___x_759_ = lean_array_push(v___y_753_, v___x_758_);
v___x_760_ = l_Lake_InitTemplate_ctorIdx(v_tmp_739_);
v___x_761_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7, &l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
v___x_762_ = lean_nat_dec_eq(v___x_760_, v___x_761_);
lean_dec(v___x_760_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_748_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_759_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
lean_inc_ref(v___x_748_);
v___x_766_ = l_Lake_joinRelative(v___x_748_, v___x_765_);
v___x_767_ = l_System_FilePath_pathExists(v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
v___x_769_ = l_IO_FS_writeFile(v___x_766_, v___x_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref_known(v___x_769_, 1);
v___x_770_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
v___x_771_ = l_Lake_joinRelative(v___x_748_, v___x_770_);
v___x_772_ = l_System_FilePath_pathExists(v___x_771_);
v___x_773_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
v___x_774_ = lean_string_append(v___x_773_, v___x_766_);
lean_dec_ref(v___x_766_);
v___x_775_ = lean_string_append(v___x_774_, v___x_756_);
v___x_776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_776_, sizeof(void*)*1, v___x_742_);
v___x_777_ = lean_array_push(v___x_759_, v___x_776_);
if (v___x_772_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
v___x_779_ = l_IO_FS_writeFile(v___x_771_, v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11));
v___x_781_ = lean_string_append(v___x_780_, v___x_771_);
lean_dec_ref(v___x_771_);
v___x_782_ = lean_string_append(v___x_781_, v___x_756_);
v___x_783_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v___x_742_);
v___x_784_ = lean_box(0);
v___x_785_ = lean_array_push(v___x_777_, v___x_783_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v___x_771_);
v_a_787_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_779_, 1);
v___x_788_ = lean_io_error_to_string(v_a_787_);
v___x_789_ = 3;
v___x_790_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*1, v___x_789_);
v___x_791_ = lean_array_get_size(v___x_777_);
v___x_792_ = lean_array_push(v___x_777_, v___x_790_);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
return v___x_793_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___x_771_);
v___x_794_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13));
v___x_795_ = lean_array_push(v___x_777_, v___x_794_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_795_);
return v___x_797_;
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v___x_766_);
lean_dec_ref(v___x_748_);
v_a_798_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_769_, 1);
v___x_799_ = lean_io_error_to_string(v_a_798_);
v___x_800_ = 3;
v___x_801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*1, v___x_800_);
v___x_802_ = lean_array_get_size(v___x_759_);
v___x_803_ = lean_array_push(v___x_759_, v___x_801_);
v___x_804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v___x_766_);
lean_dec_ref(v___x_748_);
v___x_805_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15));
v___x_806_ = lean_array_push(v___x_759_, v___x_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v___x_748_);
v_a_835_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_749_, 1);
v___x_836_ = lean_io_error_to_string(v_a_835_);
v___x_837_ = 3;
v___x_838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*1, v___x_837_);
v___x_839_ = lean_array_get_size(v___x_744_);
v___x_840_ = lean_array_push(v___x_744_, v___x_838_);
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* v_dir_842_, lean_object* v_tmp_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
uint8_t v_tmp_boxed_846_; lean_object* v_res_847_; 
v_tmp_boxed_846_ = lean_unbox(v_tmp_843_);
v_res_847_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_842_, v_tmp_boxed_846_, v_a_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* v_as_848_, size_t v_i_849_, size_t v_stop_850_, lean_object* v_b_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_eq(v_i_849_, v_stop_850_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; 
v___x_855_ = lean_array_uget_borrowed(v_as_848_, v_i_849_);
lean_inc_ref(v___y_852_);
lean_inc(v___x_855_);
v___x_856_ = lean_apply_2(v___y_852_, v___x_855_, lean_box(0));
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_849_, v___x_857_);
v_i_849_ = v___x_858_;
v_b_851_ = v___x_856_;
goto _start;
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_b_851_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* v_as_861_, lean_object* v_i_862_, lean_object* v_stop_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
size_t v_i_boxed_867_; size_t v_stop_boxed_868_; lean_object* v_res_869_; 
v_i_boxed_867_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_stop_boxed_868_ = lean_unbox_usize(v_stop_863_);
lean_dec(v_stop_863_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_861_, v_i_boxed_867_, v_stop_boxed_868_, v_b_864_, v___y_865_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v_as_861_);
return v_res_869_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_884_ = lean_array_get_size(v___x_883_);
return v___x_884_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_nat_dec_lt(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_888_; size_t v___x_889_; 
v___x_888_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_889_ = lean_usize_of_nat(v___x_888_);
return v___x_889_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_895_ = l_Lake_Git_upstreamBranch;
v___x_896_ = lean_string_dec_eq(v___x_895_, v___x_894_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14(void){
_start:
{
uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_898_ = 1;
v___x_899_ = l_Lake_InitTemplate_ctorIdx(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_906_, lean_object* v_name_907_, uint8_t v_tmp_908_, uint8_t v_lang_909_, lean_object* v_env_910_, uint8_t v_offline_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___y_916_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_944_; lean_object* v___y_945_; uint8_t v_a_946_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; uint8_t v_a_1066_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v_a_1123_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; uint8_t v_a_1152_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v_a_1251_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_configFile_1283_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v_fst_1318_; lean_object* v_snd_1319_; lean_object* v___y_1327_; lean_object* v___y_1328_; uint8_t v_a_1329_; lean_object* v___y_1335_; uint8_t v_a_1336_; lean_object* v___y_1360_; uint8_t v___x_1361_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_914_ = l_Lake_defaultConfigFile;
v___x_1281_ = l_Lake_ConfigLang_fileExtension(v_lang_909_);
v___x_1282_ = l_System_FilePath_addExtension(v___x_914_, v___x_1281_);
lean_dec_ref(v___x_1281_);
lean_inc_ref(v_dir_906_);
v_configFile_1283_ = l_Lake_joinRelative(v_dir_906_, v___x_1282_);
v___x_1361_ = l_System_FilePath_pathExists(v_configFile_1283_);
v___x_1394_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1395_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1395_ == 0)
{
goto v___jp_1362_;
}
else
{
lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1394_, v___x_1397_, v___x_1398_, v___x_1396_, v_a_912_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec_ref_known(v___x_1399_, 1);
goto v___jp_1362_;
}
else
{
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___x_1399_;
}
}
v___jp_915_:
{
if (v_offline_911_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_box(0);
v___x_920_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_906_);
v___x_921_ = l_Lake_joinRelative(v_dir_906_, v___x_920_);
lean_inc_ref(v___x_921_);
v___x_922_ = l_Lake_joinRelative(v___x_921_, v___x_914_);
v___x_923_ = l_Lake_defaultManifestFile;
v___x_924_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_925_ = lean_box(1);
v___x_926_ = l_Lean_Options_empty;
v___x_927_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_928_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_928_, 0, v_env_910_);
lean_ctor_set(v___x_928_, 1, v___x_917_);
lean_ctor_set(v___x_928_, 2, v_dir_906_);
lean_ctor_set(v___x_928_, 3, v___x_918_);
lean_ctor_set(v___x_928_, 4, v___x_919_);
lean_ctor_set(v___x_928_, 5, v___x_920_);
lean_ctor_set(v___x_928_, 6, v___x_921_);
lean_ctor_set(v___x_928_, 7, v___x_914_);
lean_ctor_set(v___x_928_, 8, v___x_922_);
lean_ctor_set(v___x_928_, 9, v___x_917_);
lean_ctor_set(v___x_928_, 10, v___x_923_);
lean_ctor_set(v___x_928_, 11, v___x_924_);
lean_ctor_set(v___x_928_, 12, v___x_925_);
lean_ctor_set(v___x_928_, 13, v___x_926_);
lean_ctor_set(v___x_928_, 14, v___x_927_);
lean_ctor_set(v___x_928_, 15, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*16, v_offline_911_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*16 + 1, v_offline_911_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*16 + 2, v_offline_911_);
v___x_929_ = l_Lean_NameSet_empty;
v___x_930_ = l_Lake_updateManifest(v___x_928_, v___x_929_, v___y_916_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
v___jp_933_:
{
if (lean_obj_tag(v___y_935_) == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_934_);
v___x_937_ = lean_apply_2(v___y_934_, v___x_936_, lean_box(0));
v___y_916_ = v___y_934_;
goto v___jp_915_;
}
else
{
lean_dec_ref_known(v___y_935_, 1);
v___y_916_ = v___y_934_;
goto v___jp_915_;
}
}
v___jp_938_:
{
switch(v_tmp_908_)
{
case 3:
{
v___y_934_ = v___y_940_;
v___y_935_ = v___y_939_;
goto v___jp_933_;
}
case 4:
{
v___y_934_ = v___y_940_;
v___y_935_ = v___y_939_;
goto v___jp_933_;
}
default: 
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v___y_939_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
v___jp_943_:
{
if (v_a_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_945_);
v___x_948_ = lean_apply_2(v___y_945_, v___x_947_, lean_box(0));
v___y_939_ = v___y_944_;
v___y_940_ = v___y_945_;
goto v___jp_938_;
}
else
{
v___y_939_ = v___y_944_;
v___y_940_ = v___y_945_;
goto v___jp_938_;
}
}
v___jp_949_:
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; 
v___x_954_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_906_);
v___x_955_ = l_Lake_joinRelative(v_dir_906_, v___x_954_);
v___x_956_ = 4;
v___x_957_ = lean_io_prim_handle_mk(v___x_955_, v___x_956_);
lean_dec_ref(v___x_955_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_960_ = lean_io_prim_handle_put_str(v_a_958_, v___x_959_);
lean_dec(v_a_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
lean_dec_ref_known(v___x_960_, 1);
v___x_961_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_906_);
v___x_962_ = l_Lake_joinRelative(v_dir_906_, v___x_961_);
v___x_963_ = lean_string_utf8_byte_size(v___y_950_);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_nat_dec_eq(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec_ref(v___y_952_);
v___x_966_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_967_ = lean_string_append(v___y_950_, v___x_966_);
v___x_968_ = l_IO_FS_writeFile(v___x_962_, v___x_967_);
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_962_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_dec_ref_known(v___x_968_, 1);
v___y_939_ = v___y_951_;
v___y_940_ = v___y_953_;
goto v___jp_938_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___y_951_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_981_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_981_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_981_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_973_ = lean_io_error_to_string(v_a_969_);
v___x_974_ = 3;
v___x_975_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_974_);
lean_inc_ref(v___y_953_);
v___x_976_ = lean_apply_2(v___y_953_, v___x_975_, lean_box(0));
v___x_977_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_977_);
v___x_979_ = v___x_971_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_githash_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
lean_dec_ref(v___y_950_);
v_githash_982_ = lean_ctor_get(v___y_952_, 1);
lean_inc_ref(v_githash_982_);
lean_dec_ref(v___y_952_);
v___x_983_ = lean_string_utf8_byte_size(v_githash_982_);
lean_dec_ref(v_githash_982_);
v___x_984_ = lean_nat_dec_eq(v___x_983_, v___x_964_);
if (v___x_984_ == 0)
{
uint8_t v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_985_ = l_System_FilePath_pathExists(v___x_962_);
lean_dec_ref(v___x_962_);
v___x_986_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_987_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_987_ == 0)
{
v___y_944_ = v___y_951_;
v___y_945_ = v___y_953_;
v_a_946_ = v___x_985_;
goto v___jp_943_;
}
else
{
lean_object* v___x_988_; size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_box(0);
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_986_, v___x_989_, v___x_990_, v___x_988_, v___y_953_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_dec_ref_known(v___x_991_, 1);
v___y_944_ = v___y_951_;
v___y_945_ = v___y_953_;
v_a_946_ = v___x_985_;
goto v___jp_943_;
}
else
{
lean_dec(v___y_951_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
return v___x_991_;
}
}
}
else
{
lean_dec_ref(v___x_962_);
v___y_939_ = v___y_951_;
v___y_940_ = v___y_953_;
goto v___jp_938_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
v_a_992_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_994_ = v___x_960_;
v_isShared_995_ = v_isSharedCheck_1004_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_960_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1004_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_996_ = lean_io_error_to_string(v_a_992_);
v___x_997_ = 3;
v___x_998_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*1, v___x_997_);
lean_inc_ref(v___y_953_);
v___x_999_ = lean_apply_2(v___y_953_, v___x_998_, lean_box(0));
v___x_1000_ = lean_box(0);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1000_);
v___x_1002_ = v___x_994_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
v_a_1005_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1007_ = v___x_957_;
v_isShared_1008_ = v_isSharedCheck_1017_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_957_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1017_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1009_ = lean_io_error_to_string(v_a_1005_);
v___x_1010_ = 3;
v___x_1011_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*1, v___x_1010_);
lean_inc_ref(v___y_953_);
v___x_1012_ = lean_apply_2(v___y_953_, v___x_1011_, lean_box(0));
v___x_1013_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1013_);
v___x_1015_ = v___x_1007_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
v___jp_1018_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11));
lean_inc_ref(v___y_1020_);
v___x_1024_ = lean_apply_2(v___y_1020_, v___x_1023_, lean_box(0));
v___y_950_ = v___y_1019_;
v___y_951_ = v___y_1021_;
v___y_952_ = v___y_1022_;
v___y_953_ = v___y_1020_;
goto v___jp_949_;
}
v___jp_1025_:
{
if (lean_obj_tag(v___y_1030_) == 0)
{
lean_dec_ref_known(v___y_1030_, 1);
v___y_950_ = v___y_1026_;
v___y_951_ = v___y_1028_;
v___y_952_ = v___y_1029_;
v___y_953_ = v___y_1027_;
goto v___jp_949_;
}
else
{
lean_dec_ref_known(v___y_1030_, 1);
v___y_1019_ = v___y_1026_;
v___y_1020_ = v___y_1027_;
v___y_1021_ = v___y_1028_;
v___y_1022_ = v___y_1029_;
goto v___jp_1018_;
}
}
v___jp_1031_:
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = l_Lake_Git_upstreamBranch;
v___x_1037_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_906_);
v___x_1040_ = l_Lake_GitRepo_checkoutBranch(v___x_1036_, v_dir_906_, v___x_1039_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 2);
v___x_1042_ = lean_array_get_size(v_a_1041_);
v___x_1043_ = lean_nat_dec_lt(v___x_1038_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec(v_a_1041_);
v___y_950_ = v___y_1032_;
v___y_951_ = v___y_1034_;
v___y_952_ = v___y_1035_;
v___y_953_ = v___y_1033_;
goto v___jp_949_;
}
else
{
lean_object* v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = ((size_t)0ULL);
v___x_1046_ = lean_usize_of_nat(v___x_1042_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1041_, v___x_1045_, v___x_1046_, v___x_1044_, v___y_1033_);
lean_dec(v_a_1041_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_dec_ref_known(v___x_1047_, 1);
v___y_950_ = v___y_1032_;
v___y_951_ = v___y_1034_;
v___y_952_ = v___y_1035_;
v___y_953_ = v___y_1033_;
goto v___jp_949_;
}
else
{
v___y_1026_ = v___y_1032_;
v___y_1027_ = v___y_1033_;
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___y_1035_;
v___y_1030_ = v___x_1047_;
goto v___jp_1025_;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_a_1048_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1040_, 2);
v___x_1049_ = lean_array_get_size(v_a_1048_);
v___x_1050_ = lean_nat_dec_lt(v___x_1038_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec(v_a_1048_);
v___y_1019_ = v___y_1032_;
v___y_1020_ = v___y_1033_;
v___y_1021_ = v___y_1034_;
v___y_1022_ = v___y_1035_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = lean_usize_of_nat(v___x_1049_);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1048_, v___x_1052_, v___x_1053_, v___x_1051_, v___y_1033_);
lean_dec(v_a_1048_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_dec_ref_known(v___x_1054_, 1);
v___y_1019_ = v___y_1032_;
v___y_1020_ = v___y_1033_;
v___y_1021_ = v___y_1034_;
v___y_1022_ = v___y_1035_;
goto v___jp_1018_;
}
else
{
v___y_1026_ = v___y_1032_;
v___y_1027_ = v___y_1033_;
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___y_1035_;
v___y_1030_ = v___x_1054_;
goto v___jp_1025_;
}
}
}
}
else
{
v___y_950_ = v___y_1032_;
v___y_951_ = v___y_1034_;
v___y_952_ = v___y_1035_;
v___y_953_ = v___y_1033_;
goto v___jp_949_;
}
}
v___jp_1055_:
{
if (lean_obj_tag(v___y_1060_) == 0)
{
lean_dec_ref_known(v___y_1060_, 1);
v___y_1032_ = v___y_1056_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1059_;
goto v___jp_1031_;
}
else
{
lean_dec_ref_known(v___y_1060_, 1);
v___y_1019_ = v___y_1056_;
v___y_1020_ = v___y_1057_;
v___y_1021_ = v___y_1058_;
v___y_1022_ = v___y_1059_;
goto v___jp_1018_;
}
}
v___jp_1061_:
{
if (v_a_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_906_);
v___x_1069_ = l_Lake_GitRepo_quietInit(v_dir_906_, v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1071_ = lean_array_get_size(v_a_1070_);
v___x_1072_ = lean_nat_dec_lt(v___x_1067_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec(v_a_1070_);
v___y_1032_ = v___y_1062_;
v___y_1033_ = v___y_1063_;
v___y_1034_ = v___y_1064_;
v___y_1035_ = v___y_1065_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = lean_usize_of_nat(v___x_1071_);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1070_, v___x_1074_, v___x_1075_, v___x_1073_, v___y_1063_);
lean_dec(v_a_1070_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_dec_ref_known(v___x_1076_, 1);
v___y_1032_ = v___y_1062_;
v___y_1033_ = v___y_1063_;
v___y_1034_ = v___y_1064_;
v___y_1035_ = v___y_1065_;
goto v___jp_1031_;
}
else
{
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1063_;
v___y_1058_ = v___y_1064_;
v___y_1059_ = v___y_1065_;
v___y_1060_ = v___x_1076_;
goto v___jp_1055_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_a_1077_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1078_ = lean_array_get_size(v_a_1077_);
v___x_1079_ = lean_nat_dec_lt(v___x_1067_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec(v_a_1077_);
v___y_1019_ = v___y_1062_;
v___y_1020_ = v___y_1063_;
v___y_1021_ = v___y_1064_;
v___y_1022_ = v___y_1065_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1078_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1077_, v___x_1081_, v___x_1082_, v___x_1080_, v___y_1063_);
lean_dec(v_a_1077_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_dec_ref_known(v___x_1083_, 1);
v___y_1019_ = v___y_1062_;
v___y_1020_ = v___y_1063_;
v___y_1021_ = v___y_1064_;
v___y_1022_ = v___y_1065_;
goto v___jp_1018_;
}
else
{
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1063_;
v___y_1058_ = v___y_1064_;
v___y_1059_ = v___y_1065_;
v___y_1060_ = v___x_1083_;
goto v___jp_1055_;
}
}
}
}
else
{
v___y_950_ = v___y_1062_;
v___y_951_ = v___y_1064_;
v___y_952_ = v___y_1065_;
v___y_953_ = v___y_1063_;
goto v___jp_949_;
}
}
v___jp_1084_:
{
uint8_t v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
lean_inc_ref(v_dir_906_);
v___x_1089_ = l_Lake_GitRepo_insideWorkTree(v_dir_906_);
v___x_1090_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1091_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1091_ == 0)
{
v___y_1062_ = v___y_1085_;
v___y_1063_ = v___y_1088_;
v___y_1064_ = v___y_1086_;
v___y_1065_ = v___y_1087_;
v_a_1066_ = v___x_1089_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1090_, v___x_1093_, v___x_1094_, v___x_1092_, v___y_1088_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref_known(v___x_1095_, 1);
v___y_1062_ = v___y_1085_;
v___y_1063_ = v___y_1088_;
v___y_1064_ = v___y_1086_;
v___y_1065_ = v___y_1087_;
v_a_1066_ = v___x_1089_;
goto v___jp_1061_;
}
else
{
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
return v___x_1095_;
}
}
}
v___jp_1096_:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_IO_FS_writeFile(v___y_1099_, v___y_1102_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___y_1099_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref_known(v___x_1103_, 1);
v___y_1085_ = v___y_1097_;
v___y_1086_ = v___y_1100_;
v___y_1087_ = v___y_1101_;
v___y_1088_ = v___y_1098_;
goto v___jp_1084_;
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v_env_910_);
lean_dec_ref(v_dir_906_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1116_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1116_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1108_ = lean_io_error_to_string(v_a_1104_);
v___x_1109_ = 3;
v___x_1110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*1, v___x_1109_);
lean_inc_ref(v___y_1098_);
v___x_1111_ = lean_apply_2(v___y_1098_, v___x_1110_, lean_box(0));
v___x_1112_ = lean_box(0);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1112_);
v___x_1114_ = v___x_1106_;
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
v___jp_1117_:
{
if (v_a_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = l_Lake_InitTemplate_ctorIdx(v_tmp_908_);
v___x_1125_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7, &l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
v___x_1126_ = lean_nat_dec_eq(v___x_1124_, v___x_1125_);
lean_dec(v___x_1124_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_907_);
v___x_1128_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1127_);
lean_dec_ref(v___x_1127_);
v___y_1097_ = v___y_1118_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1120_;
v___y_1100_ = v___y_1121_;
v___y_1101_ = v___y_1122_;
v___y_1102_ = v___x_1128_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_907_);
v___x_1130_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1129_);
lean_dec_ref(v___x_1129_);
v___y_1097_ = v___y_1118_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1120_;
v___y_1100_ = v___y_1121_;
v___y_1101_ = v___y_1122_;
v___y_1102_ = v___x_1130_;
goto v___jp_1096_;
}
}
else
{
lean_dec_ref(v___y_1120_);
lean_dec(v_name_907_);
v___y_1085_ = v___y_1118_;
v___y_1086_ = v___y_1121_;
v___y_1087_ = v___y_1122_;
v___y_1088_ = v___y_1119_;
goto v___jp_1084_;
}
}
v___jp_1131_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1136_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_906_);
v___x_1137_ = l_Lake_joinRelative(v_dir_906_, v___x_1136_);
v___x_1138_ = l_System_FilePath_pathExists(v___x_1137_);
v___x_1139_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1140_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1140_ == 0)
{
v___y_1118_ = v___y_1132_;
v___y_1119_ = v___y_1135_;
v___y_1120_ = v___x_1137_;
v___y_1121_ = v___y_1133_;
v___y_1122_ = v___y_1134_;
v_a_1123_ = v___x_1138_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1139_, v___x_1142_, v___x_1143_, v___x_1141_, v___y_1135_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec_ref_known(v___x_1144_, 1);
v___y_1118_ = v___y_1132_;
v___y_1119_ = v___y_1135_;
v___y_1120_ = v___x_1137_;
v___y_1121_ = v___y_1133_;
v___y_1122_ = v___y_1134_;
v_a_1123_ = v___x_1138_;
goto v___jp_1117_;
}
else
{
lean_dec_ref(v___x_1137_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___x_1144_;
}
}
}
v___jp_1145_:
{
if (v_a_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = l_Lake_InitTemplate_ctorIdx(v_tmp_908_);
v___x_1154_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14);
v___x_1155_ = lean_nat_dec_eq(v___x_1153_, v___x_1154_);
lean_dec(v___x_1153_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1148_);
v___x_1157_ = l_IO_FS_writeFile(v___y_1149_, v___x_1156_);
lean_dec_ref(v___x_1156_);
lean_dec_ref(v___y_1149_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_dec_ref_known(v___x_1157_, 1);
v___y_1132_ = v___y_1146_;
v___y_1133_ = v___y_1150_;
v___y_1134_ = v___y_1151_;
v___y_1135_ = v___y_1147_;
goto v___jp_1131_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1162_ = lean_io_error_to_string(v_a_1158_);
v___x_1163_ = 3;
v___x_1164_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*1, v___x_1163_);
lean_inc_ref(v___y_1147_);
v___x_1165_ = lean_apply_2(v___y_1147_, v___x_1164_, lean_box(0));
v___x_1166_ = lean_box(0);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1166_);
v___x_1168_ = v___x_1160_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v___y_1148_);
v___x_1171_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1172_ = l_IO_FS_writeFile(v___y_1149_, v___x_1171_);
lean_dec_ref(v___y_1149_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_dec_ref_known(v___x_1172_, 1);
v___y_1132_ = v___y_1146_;
v___y_1133_ = v___y_1150_;
v___y_1134_ = v___y_1151_;
v___y_1135_ = v___y_1147_;
goto v___jp_1131_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1185_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1185_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1177_ = lean_io_error_to_string(v_a_1173_);
v___x_1178_ = 3;
v___x_1179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*1, v___x_1178_);
lean_inc_ref(v___y_1147_);
v___x_1180_ = lean_apply_2(v___y_1147_, v___x_1179_, lean_box(0));
v___x_1181_ = lean_box(0);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1181_);
v___x_1183_ = v___x_1175_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
v___y_1132_ = v___y_1146_;
v___y_1133_ = v___y_1150_;
v___y_1134_ = v___y_1151_;
v___y_1135_ = v___y_1147_;
goto v___jp_1131_;
}
}
v___jp_1186_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1192_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_906_);
v___x_1193_ = l_Lake_joinRelative(v_dir_906_, v___x_1192_);
v___x_1194_ = l_System_FilePath_pathExists(v___x_1193_);
v___x_1195_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1196_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1196_ == 0)
{
v___y_1146_ = v___y_1187_;
v___y_1147_ = v___y_1189_;
v___y_1148_ = v___y_1188_;
v___y_1149_ = v___x_1193_;
v___y_1150_ = v___y_1190_;
v___y_1151_ = v___y_1191_;
v_a_1152_ = v___x_1194_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = ((size_t)0ULL);
v___x_1199_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1195_, v___x_1198_, v___x_1199_, v___x_1197_, v___y_1189_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_dec_ref_known(v___x_1200_, 1);
v___y_1146_ = v___y_1187_;
v___y_1147_ = v___y_1189_;
v___y_1148_ = v___y_1188_;
v___y_1149_ = v___x_1193_;
v___y_1150_ = v___y_1190_;
v___y_1151_ = v___y_1191_;
v_a_1152_ = v___x_1194_;
goto v___jp_1145_;
}
else
{
lean_dec_ref(v___x_1193_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___x_1200_;
}
}
}
v___jp_1201_:
{
switch(v_tmp_908_)
{
case 0:
{
v___y_1187_ = v___y_1202_;
v___y_1188_ = v___y_1203_;
v___y_1189_ = v___y_1206_;
v___y_1190_ = v___y_1204_;
v___y_1191_ = v___y_1205_;
goto v___jp_1186_;
}
case 1:
{
v___y_1187_ = v___y_1202_;
v___y_1188_ = v___y_1203_;
v___y_1189_ = v___y_1206_;
v___y_1190_ = v___y_1204_;
v___y_1191_ = v___y_1205_;
goto v___jp_1186_;
}
default: 
{
lean_dec(v___y_1203_);
v___y_1132_ = v___y_1202_;
v___y_1133_ = v___y_1204_;
v___y_1134_ = v___y_1205_;
v___y_1135_ = v___y_1206_;
goto v___jp_1131_;
}
}
}
v___jp_1207_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_IO_FS_writeFile(v___y_1212_, v___y_1214_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___y_1212_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec_ref_known(v___x_1215_, 1);
v___y_1202_ = v___y_1208_;
v___y_1203_ = v___y_1209_;
v___y_1204_ = v___y_1210_;
v___y_1205_ = v___y_1213_;
v___y_1206_ = v___y_1211_;
goto v___jp_1201_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1228_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1228_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1220_ = lean_io_error_to_string(v_a_1216_);
v___x_1221_ = 3;
v___x_1222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set_uint8(v___x_1222_, sizeof(void*)*1, v___x_1221_);
lean_inc_ref(v___y_1211_);
v___x_1223_ = lean_apply_2(v___y_1211_, v___x_1222_, lean_box(0));
v___x_1224_ = lean_box(0);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1224_);
v___x_1226_ = v___x_1218_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
v___jp_1229_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = l_Lake_InitTemplate_ctorIdx(v_tmp_908_);
v___x_1237_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7, &l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
v___x_1238_ = lean_nat_dec_eq(v___x_1236_, v___x_1237_);
lean_dec(v___x_1236_);
if (v___x_1238_ == 0)
{
uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = 1;
lean_inc_n(v___y_1231_, 2);
v___x_1240_ = l_Lean_Name_toString(v___y_1231_, v___x_1239_);
v___x_1241_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1240_, v___y_1231_);
lean_dec_ref(v___x_1240_);
v___y_1208_ = v___y_1230_;
v___y_1209_ = v___y_1231_;
v___y_1210_ = v___y_1232_;
v___y_1211_ = v___y_1235_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1234_;
v___y_1214_ = v___x_1241_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1242_; 
lean_inc(v___y_1231_);
v___x_1242_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1231_);
v___y_1208_ = v___y_1230_;
v___y_1209_ = v___y_1231_;
v___y_1210_ = v___y_1232_;
v___y_1211_ = v___y_1235_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1234_;
v___y_1214_ = v___x_1242_;
goto v___jp_1207_;
}
}
v___jp_1243_:
{
if (v_a_1251_ == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = l_IO_FS_createDirAll(v___y_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1252_, 1);
v___x_1253_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1254_ = l_IO_FS_writeFile(v___y_1245_, v___x_1253_);
lean_dec_ref(v___y_1245_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec_ref_known(v___x_1254_, 1);
v___y_1230_ = v___y_1244_;
v___y_1231_ = v___y_1246_;
v___y_1232_ = v___y_1247_;
v___y_1233_ = v___y_1249_;
v___y_1234_ = v___y_1250_;
v___y_1235_ = v_a_912_;
goto v___jp_1229_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1259_ = lean_io_error_to_string(v_a_1255_);
v___x_1260_ = 3;
v___x_1261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*1, v___x_1260_);
lean_inc_ref(v_a_912_);
v___x_1262_ = lean_apply_2(v_a_912_, v___x_1261_, lean_box(0));
v___x_1263_ = lean_box(0);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1263_);
v___x_1265_ = v___x_1257_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_a_1268_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1270_ = v___x_1252_;
v_isShared_1271_ = v_isSharedCheck_1280_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1252_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1280_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1272_ = lean_io_error_to_string(v_a_1268_);
v___x_1273_ = 3;
v___x_1274_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*1, v___x_1273_);
lean_inc_ref(v_a_912_);
v___x_1275_ = lean_apply_2(v_a_912_, v___x_1274_, lean_box(0));
v___x_1276_ = lean_box(0);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1276_);
v___x_1278_ = v___x_1270_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_dec_ref(v___y_1248_);
lean_dec_ref(v___y_1245_);
v___y_1230_ = v___y_1244_;
v___y_1231_ = v___y_1246_;
v___y_1232_ = v___y_1247_;
v___y_1233_ = v___y_1249_;
v___y_1234_ = v___y_1250_;
v___y_1235_ = v_a_912_;
goto v___jp_1229_;
}
}
v___jp_1284_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v___y_1289_);
lean_inc(v___y_1286_);
lean_inc(v_name_907_);
v___x_1290_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_908_, v_lang_909_, v_name_907_, v___y_1286_, v___y_1289_);
v___x_1291_ = l_IO_FS_writeFile(v_configFile_1283_, v___x_1290_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_configFile_1283_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_dec_ref_known(v___x_1291_, 1);
if (lean_obj_tag(v___y_1287_) == 1)
{
lean_object* v_val_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_val_1292_ = lean_ctor_get(v___y_1287_, 0);
lean_inc_n(v_val_1292_, 2);
lean_dec_ref_known(v___y_1287_, 1);
v___x_1293_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1294_ = l_System_FilePath_withExtension(v_val_1292_, v___x_1293_);
v___x_1295_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_1294_);
v___x_1296_ = l_Lake_joinRelative(v___x_1294_, v___x_1295_);
v___x_1297_ = l_System_FilePath_pathExists(v___x_1296_);
v___x_1298_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1299_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1299_ == 0)
{
v___y_1244_ = v___y_1285_;
v___y_1245_ = v___x_1296_;
v___y_1246_ = v___y_1286_;
v___y_1247_ = v___y_1289_;
v___y_1248_ = v___x_1294_;
v___y_1249_ = v_val_1292_;
v___y_1250_ = v___y_1288_;
v_a_1251_ = v___x_1297_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1298_, v___x_1301_, v___x_1302_, v___x_1300_, v_a_912_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec_ref_known(v___x_1303_, 1);
v___y_1244_ = v___y_1285_;
v___y_1245_ = v___x_1296_;
v___y_1246_ = v___y_1286_;
v___y_1247_ = v___y_1289_;
v___y_1248_ = v___x_1294_;
v___y_1249_ = v_val_1292_;
v___y_1250_ = v___y_1288_;
v_a_1251_ = v___x_1297_;
goto v___jp_1243_;
}
else
{
lean_dec_ref(v___x_1296_);
lean_dec_ref(v___x_1294_);
lean_dec(v_val_1292_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___x_1303_;
}
}
}
else
{
lean_dec(v___y_1287_);
v___y_1202_ = v___y_1285_;
v___y_1203_ = v___y_1286_;
v___y_1204_ = v___y_1289_;
v___y_1205_ = v___y_1288_;
v___y_1206_ = v_a_912_;
goto v___jp_1201_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_a_1304_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1306_ = v___x_1291_;
v_isShared_1307_ = v_isSharedCheck_1316_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1291_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1316_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1308_ = lean_io_error_to_string(v_a_1304_);
v___x_1309_ = 3;
v___x_1310_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*1, v___x_1309_);
lean_inc_ref(v_a_912_);
v___x_1311_ = lean_apply_2(v_a_912_, v___x_1310_, lean_box(0));
v___x_1312_ = lean_box(0);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1312_);
v___x_1314_ = v___x_1306_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
v___jp_1317_:
{
lean_object* v_lean_1320_; lean_object* v_toolchain_1321_; lean_object* v___x_1322_; 
v_lean_1320_ = lean_ctor_get(v_env_910_, 1);
v_toolchain_1321_ = lean_ctor_get(v_env_910_, 19);
lean_inc_ref(v_toolchain_1321_);
v___x_1322_ = l_Lake_ToolchainVer_ofString(v_toolchain_1321_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_ver_1323_; lean_object* v___x_1324_; 
v_ver_1323_ = lean_ctor_get(v___x_1322_, 1);
lean_inc_ref(v_ver_1323_);
lean_dec_ref_known(v___x_1322_, 2);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_ver_1323_);
lean_inc_ref(v_lean_1320_);
lean_inc_ref(v_toolchain_1321_);
v___y_1285_ = v_toolchain_1321_;
v___y_1286_ = v_fst_1318_;
v___y_1287_ = v_snd_1319_;
v___y_1288_ = v_lean_1320_;
v___y_1289_ = v___x_1324_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v___x_1322_);
v___x_1325_ = lean_box(0);
lean_inc_ref(v_lean_1320_);
lean_inc_ref(v_toolchain_1321_);
v___y_1285_ = v_toolchain_1321_;
v___y_1286_ = v_fst_1318_;
v___y_1287_ = v_snd_1319_;
v___y_1288_ = v_lean_1320_;
v___y_1289_ = v___x_1325_;
goto v___jp_1284_;
}
}
v___jp_1326_:
{
if (v_a_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___y_1327_);
v_fst_1318_ = v___y_1328_;
v_snd_1319_ = v___x_1330_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v___y_1327_);
v___x_1331_ = lean_box(0);
v_fst_1318_ = v___y_1328_;
v_snd_1319_ = v___x_1331_;
goto v___jp_1317_;
}
}
v___jp_1332_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_box(0);
lean_inc(v_name_907_);
v_fst_1318_ = v_name_907_;
v_snd_1319_ = v___x_1333_;
goto v___jp_1317_;
}
v___jp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = l_Lake_InitTemplate_ctorIdx(v_tmp_908_);
v___x_1338_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14);
v___x_1339_ = lean_nat_dec_eq(v___x_1337_, v___x_1338_);
lean_dec(v___x_1337_);
if (v___x_1339_ == 0)
{
if (v_a_1336_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
lean_inc(v_name_907_);
v___x_1340_ = l_Lake_toUpperCamelCase(v_name_907_);
lean_inc(v___x_1340_);
v___x_1341_ = l_Lean_modToFilePath(v_dir_906_, v___x_1340_, v___y_1335_);
v___x_1342_ = l_System_FilePath_pathExists(v___x_1341_);
v___x_1343_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1344_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1344_ == 0)
{
v___y_1327_ = v___x_1341_;
v___y_1328_ = v___x_1340_;
v_a_1329_ = v___x_1342_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1343_, v___x_1346_, v___x_1347_, v___x_1345_, v_a_912_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_dec_ref_known(v___x_1348_, 1);
v___y_1327_ = v___x_1341_;
v___y_1328_ = v___x_1340_;
v_a_1329_ = v___x_1342_;
goto v___jp_1326_;
}
else
{
lean_dec_ref(v___x_1341_);
lean_dec(v___x_1340_);
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___x_1348_;
}
}
}
else
{
goto v___jp_1332_;
}
}
else
{
goto v___jp_1332_;
}
}
v___jp_1349_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1350_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_907_);
v___x_1351_ = l_Lean_modToFilePath(v_dir_906_, v_name_907_, v___x_1350_);
v___x_1352_ = l_System_FilePath_pathExists(v___x_1351_);
lean_dec_ref(v___x_1351_);
v___x_1353_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1354_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1354_ == 0)
{
v___y_1335_ = v___x_1350_;
v_a_1336_ = v___x_1352_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1353_, v___x_1356_, v___x_1357_, v___x_1355_, v_a_912_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref_known(v___x_1358_, 1);
v___y_1335_ = v___x_1350_;
v_a_1336_ = v___x_1352_;
goto v___jp_1334_;
}
else
{
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___x_1358_;
}
}
}
v___jp_1359_:
{
if (lean_obj_tag(v___y_1360_) == 0)
{
lean_dec_ref_known(v___y_1360_, 1);
goto v___jp_1349_;
}
else
{
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
return v___y_1360_;
}
}
v___jp_1362_:
{
if (v___x_1361_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_906_);
v___x_1365_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_906_, v_tmp_908_, v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 2);
v___x_1367_ = lean_array_get_size(v_a_1366_);
v___x_1368_ = lean_nat_dec_lt(v___x_1363_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_a_1366_);
goto v___jp_1349_;
}
else
{
lean_object* v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = lean_usize_of_nat(v___x_1367_);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1366_, v___x_1370_, v___x_1371_, v___x_1369_, v_a_912_);
lean_dec(v_a_1366_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_dec_ref_known(v___x_1372_, 1);
goto v___jp_1349_;
}
else
{
v___y_1360_ = v___x_1372_;
goto v___jp_1359_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_a_1373_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1365_, 2);
v___x_1374_ = lean_array_get_size(v_a_1373_);
v___x_1375_ = lean_nat_dec_lt(v___x_1363_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_a_1373_);
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = lean_usize_of_nat(v___x_1374_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1373_, v___x_1379_, v___x_1380_, v___x_1378_, v_a_912_);
lean_dec(v_a_1373_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1389_);
v___x_1383_ = v___x_1381_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1381_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 1);
lean_ctor_set(v___x_1383_, 0, v___x_1378_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1378_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
v___y_1360_ = v___x_1381_;
goto v___jp_1359_;
}
}
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_configFile_1283_);
lean_dec_ref(v_env_910_);
lean_dec(v_name_907_);
lean_dec_ref(v_dir_906_);
v___x_1390_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
lean_inc_ref(v_a_912_);
v___x_1391_ = lean_apply_2(v_a_912_, v___x_1390_, lean_box(0));
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
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
lean_object* v___x_1573_; lean_object* v___y_1575_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1603_; lean_object* v___y_1604_; uint8_t v_a_1605_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; uint8_t v_a_1725_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; uint8_t v_a_1782_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v_a_1811_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v_a_1910_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_configFile_1942_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v___y_1986_; lean_object* v___y_1987_; uint8_t v_a_1988_; lean_object* v___y_1994_; uint8_t v_a_1995_; lean_object* v___y_2019_; uint8_t v___x_2020_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_1573_ = l_Lake_defaultConfigFile;
v___x_1940_ = l_Lake_ConfigLang_fileExtension(v_lang_1569_);
v___x_1941_ = l_System_FilePath_addExtension(v___x_1573_, v___x_1940_);
lean_dec_ref(v___x_1940_);
lean_inc_ref(v_dir_1566_);
v_configFile_1942_ = l_Lake_joinRelative(v_dir_1566_, v___x_1941_);
v___x_2020_ = l_System_FilePath_pathExists(v_configFile_1942_);
v___x_2053_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2054_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2054_ == 0)
{
goto v___jp_2021_;
}
else
{
lean_object* v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v___x_2055_ = lean_box(0);
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2053_, v___x_2056_, v___x_2057_, v___x_2055_, v_a_1565_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_dec_ref_known(v___x_2058_, 1);
goto v___jp_2021_;
}
else
{
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_2058_;
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
lean_inc_ref(v___y_1604_);
v___x_1607_ = lean_apply_2(v___y_1604_, v___x_1606_, lean_box(0));
v___y_1598_ = v___y_1603_;
v___y_1599_ = v___y_1604_;
goto v___jp_1597_;
}
else
{
v___y_1598_ = v___y_1603_;
v___y_1599_ = v___y_1604_;
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
v___x_1622_ = lean_string_utf8_byte_size(v___y_1609_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_nat_dec_eq(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v___y_1610_);
v___x_1625_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1626_ = lean_string_append(v___y_1609_, v___x_1625_);
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
lean_dec_ref(v___y_1609_);
v_githash_1641_ = lean_ctor_get(v___y_1610_, 1);
lean_inc_ref(v_githash_1641_);
lean_dec_ref(v___y_1610_);
v___x_1642_ = lean_string_utf8_byte_size(v_githash_1641_);
lean_dec_ref(v_githash_1641_);
v___x_1643_ = lean_nat_dec_eq(v___x_1642_, v___x_1623_);
if (v___x_1643_ == 0)
{
uint8_t v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1644_ = l_System_FilePath_pathExists(v___x_1621_);
lean_dec_ref(v___x_1621_);
v___x_1645_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1646_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1646_ == 0)
{
v___y_1603_ = v___y_1611_;
v___y_1604_ = v___y_1612_;
v_a_1605_ = v___x_1644_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = lean_box(0);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1645_, v___x_1648_, v___x_1649_, v___x_1647_, v___y_1612_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_dec_ref_known(v___x_1650_, 1);
v___y_1603_ = v___y_1611_;
v___y_1604_ = v___y_1612_;
v_a_1605_ = v___x_1644_;
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
lean_inc_ref(v___y_1681_);
v___x_1683_ = lean_apply_2(v___y_1681_, v___x_1682_, lean_box(0));
v___y_1609_ = v___y_1678_;
v___y_1610_ = v___y_1679_;
v___y_1611_ = v___y_1680_;
v___y_1612_ = v___y_1681_;
goto v___jp_1608_;
}
v___jp_1684_:
{
if (lean_obj_tag(v___y_1689_) == 0)
{
lean_dec_ref_known(v___y_1689_, 1);
v___y_1609_ = v___y_1685_;
v___y_1610_ = v___y_1686_;
v___y_1611_ = v___y_1687_;
v___y_1612_ = v___y_1688_;
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
v___y_1609_ = v___y_1691_;
v___y_1610_ = v___y_1692_;
v___y_1611_ = v___y_1693_;
v___y_1612_ = v___y_1694_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = lean_usize_of_nat(v___x_1701_);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1700_, v___x_1704_, v___x_1705_, v___x_1703_, v___y_1694_);
lean_dec(v_a_1700_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_dec_ref_known(v___x_1706_, 1);
v___y_1609_ = v___y_1691_;
v___y_1610_ = v___y_1692_;
v___y_1611_ = v___y_1693_;
v___y_1612_ = v___y_1694_;
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
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1707_, v___x_1711_, v___x_1712_, v___x_1710_, v___y_1694_);
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
v___y_1609_ = v___y_1691_;
v___y_1610_ = v___y_1692_;
v___y_1611_ = v___y_1693_;
v___y_1612_ = v___y_1694_;
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
v___y_1693_ = v___y_1717_;
v___y_1694_ = v___y_1718_;
goto v___jp_1690_;
}
else
{
lean_dec_ref_known(v___y_1719_, 1);
v___y_1678_ = v___y_1715_;
v___y_1679_ = v___y_1716_;
v___y_1680_ = v___y_1717_;
v___y_1681_ = v___y_1718_;
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
v___y_1693_ = v___y_1723_;
v___y_1694_ = v___y_1724_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_box(0);
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = lean_usize_of_nat(v___x_1730_);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1729_, v___x_1733_, v___x_1734_, v___x_1732_, v___y_1724_);
lean_dec(v_a_1729_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_dec_ref_known(v___x_1735_, 1);
v___y_1691_ = v___y_1721_;
v___y_1692_ = v___y_1722_;
v___y_1693_ = v___y_1723_;
v___y_1694_ = v___y_1724_;
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
v___y_1680_ = v___y_1723_;
v___y_1681_ = v___y_1724_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = lean_usize_of_nat(v___x_1737_);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1736_, v___x_1740_, v___x_1741_, v___x_1739_, v___y_1724_);
lean_dec(v_a_1736_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_dec_ref_known(v___x_1742_, 1);
v___y_1678_ = v___y_1721_;
v___y_1679_ = v___y_1722_;
v___y_1680_ = v___y_1723_;
v___y_1681_ = v___y_1724_;
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
v___y_1609_ = v___y_1721_;
v___y_1610_ = v___y_1722_;
v___y_1611_ = v___y_1723_;
v___y_1612_ = v___y_1724_;
goto v___jp_1608_;
}
}
v___jp_1743_:
{
uint8_t v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
lean_inc_ref(v_dir_1566_);
v___x_1748_ = l_Lake_GitRepo_insideWorkTree(v_dir_1566_);
v___x_1749_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1750_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1750_ == 0)
{
v___y_1721_ = v___y_1744_;
v___y_1722_ = v___y_1745_;
v___y_1723_ = v___y_1746_;
v___y_1724_ = v___y_1747_;
v_a_1725_ = v___x_1748_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1749_, v___x_1752_, v___x_1753_, v___x_1751_, v___y_1747_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_dec_ref_known(v___x_1754_, 1);
v___y_1721_ = v___y_1744_;
v___y_1722_ = v___y_1745_;
v___y_1723_ = v___y_1746_;
v___y_1724_ = v___y_1747_;
v_a_1725_ = v___x_1748_;
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
v___x_1762_ = l_IO_FS_writeFile(v___y_1756_, v___y_1761_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1756_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_dec_ref_known(v___x_1762_, 1);
v___y_1744_ = v___y_1757_;
v___y_1745_ = v___y_1759_;
v___y_1746_ = v___y_1760_;
v___y_1747_ = v___y_1758_;
goto v___jp_1743_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
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
lean_inc_ref(v___y_1758_);
v___x_1770_ = lean_apply_2(v___y_1758_, v___x_1769_, lean_box(0));
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
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = l_Lake_InitTemplate_ctorIdx(v_tmp_1568_);
v___x_1784_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7, &l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
v___x_1785_ = lean_nat_dec_eq(v___x_1783_, v___x_1784_);
lean_dec(v___x_1783_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1567_);
v___x_1787_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1786_);
lean_dec_ref(v___x_1786_);
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1779_;
v___y_1758_ = v___y_1778_;
v___y_1759_ = v___y_1780_;
v___y_1760_ = v___y_1781_;
v___y_1761_ = v___x_1787_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1567_);
v___x_1789_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1788_);
lean_dec_ref(v___x_1788_);
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1779_;
v___y_1758_ = v___y_1778_;
v___y_1759_ = v___y_1780_;
v___y_1760_ = v___y_1781_;
v___y_1761_ = v___x_1789_;
goto v___jp_1755_;
}
}
else
{
lean_dec_ref(v___y_1777_);
lean_dec(v_name_1567_);
v___y_1744_ = v___y_1779_;
v___y_1745_ = v___y_1780_;
v___y_1746_ = v___y_1781_;
v___y_1747_ = v___y_1778_;
goto v___jp_1743_;
}
}
v___jp_1790_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1795_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13));
lean_inc_ref(v_dir_1566_);
v___x_1796_ = l_Lake_joinRelative(v_dir_1566_, v___x_1795_);
v___x_1797_ = l_System_FilePath_pathExists(v___x_1796_);
v___x_1798_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1799_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1799_ == 0)
{
v___y_1777_ = v___x_1796_;
v___y_1778_ = v___y_1794_;
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___y_1793_;
v_a_1782_ = v___x_1797_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = lean_box(0);
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1798_, v___x_1801_, v___x_1802_, v___x_1800_, v___y_1794_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_dec_ref_known(v___x_1803_, 1);
v___y_1777_ = v___x_1796_;
v___y_1778_ = v___y_1794_;
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___y_1793_;
v_a_1782_ = v___x_1797_;
goto v___jp_1776_;
}
else
{
lean_dec_ref(v___x_1796_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_1803_;
}
}
}
v___jp_1804_:
{
if (v_a_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = l_Lake_InitTemplate_ctorIdx(v_tmp_1568_);
v___x_1813_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14);
v___x_1814_ = lean_nat_dec_eq(v___x_1812_, v___x_1813_);
lean_dec(v___x_1812_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1810_);
v___x_1816_ = l_IO_FS_writeFile(v___y_1805_, v___x_1815_);
lean_dec_ref(v___x_1815_);
lean_dec_ref(v___y_1805_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_dec_ref_known(v___x_1816_, 1);
v___y_1791_ = v___y_1806_;
v___y_1792_ = v___y_1807_;
v___y_1793_ = v___y_1809_;
v___y_1794_ = v___y_1808_;
goto v___jp_1790_;
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1829_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1829_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1821_ = lean_io_error_to_string(v_a_1817_);
v___x_1822_ = 3;
v___x_1823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set_uint8(v___x_1823_, sizeof(void*)*1, v___x_1822_);
lean_inc_ref(v___y_1808_);
v___x_1824_ = lean_apply_2(v___y_1808_, v___x_1823_, lean_box(0));
v___x_1825_ = lean_box(0);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1825_);
v___x_1827_ = v___x_1819_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec(v___y_1810_);
v___x_1830_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1831_ = l_IO_FS_writeFile(v___y_1805_, v___x_1830_);
lean_dec_ref(v___y_1805_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref_known(v___x_1831_, 1);
v___y_1791_ = v___y_1806_;
v___y_1792_ = v___y_1807_;
v___y_1793_ = v___y_1809_;
v___y_1794_ = v___y_1808_;
goto v___jp_1790_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1836_ = lean_io_error_to_string(v_a_1832_);
v___x_1837_ = 3;
v___x_1838_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set_uint8(v___x_1838_, sizeof(void*)*1, v___x_1837_);
lean_inc_ref(v___y_1808_);
v___x_1839_ = lean_apply_2(v___y_1808_, v___x_1838_, lean_box(0));
v___x_1840_ = lean_box(0);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1840_);
v___x_1842_ = v___x_1834_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
else
{
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1805_);
v___y_1791_ = v___y_1806_;
v___y_1792_ = v___y_1807_;
v___y_1793_ = v___y_1809_;
v___y_1794_ = v___y_1808_;
goto v___jp_1790_;
}
}
v___jp_1845_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1851_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1566_);
v___x_1852_ = l_Lake_joinRelative(v_dir_1566_, v___x_1851_);
v___x_1853_ = l_System_FilePath_pathExists(v___x_1852_);
v___x_1854_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1855_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1855_ == 0)
{
v___y_1805_ = v___x_1852_;
v___y_1806_ = v___y_1846_;
v___y_1807_ = v___y_1847_;
v___y_1808_ = v___y_1848_;
v___y_1809_ = v___y_1849_;
v___y_1810_ = v___y_1850_;
v_a_1811_ = v___x_1853_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1854_, v___x_1857_, v___x_1858_, v___x_1856_, v___y_1848_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_dec_ref_known(v___x_1859_, 1);
v___y_1805_ = v___x_1852_;
v___y_1806_ = v___y_1846_;
v___y_1807_ = v___y_1847_;
v___y_1808_ = v___y_1848_;
v___y_1809_ = v___y_1849_;
v___y_1810_ = v___y_1850_;
v_a_1811_ = v___x_1853_;
goto v___jp_1804_;
}
else
{
lean_dec_ref(v___x_1852_);
lean_dec(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_1859_;
}
}
}
v___jp_1860_:
{
switch(v_tmp_1568_)
{
case 0:
{
v___y_1846_ = v___y_1861_;
v___y_1847_ = v___y_1862_;
v___y_1848_ = v___y_1865_;
v___y_1849_ = v___y_1863_;
v___y_1850_ = v___y_1864_;
goto v___jp_1845_;
}
case 1:
{
v___y_1846_ = v___y_1861_;
v___y_1847_ = v___y_1862_;
v___y_1848_ = v___y_1865_;
v___y_1849_ = v___y_1863_;
v___y_1850_ = v___y_1864_;
goto v___jp_1845_;
}
default: 
{
lean_dec(v___y_1864_);
v___y_1791_ = v___y_1861_;
v___y_1792_ = v___y_1862_;
v___y_1793_ = v___y_1863_;
v___y_1794_ = v___y_1865_;
goto v___jp_1790_;
}
}
}
v___jp_1866_:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_IO_FS_writeFile(v___y_1871_, v___y_1873_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v___y_1871_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref_known(v___x_1874_, 1);
v___y_1861_ = v___y_1867_;
v___y_1862_ = v___y_1868_;
v___y_1863_ = v___y_1869_;
v___y_1864_ = v___y_1872_;
v___y_1865_ = v___y_1870_;
goto v___jp_1860_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v___y_1872_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1887_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1887_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1879_ = lean_io_error_to_string(v_a_1875_);
v___x_1880_ = 3;
v___x_1881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*1, v___x_1880_);
lean_inc_ref(v___y_1870_);
v___x_1882_ = lean_apply_2(v___y_1870_, v___x_1881_, lean_box(0));
v___x_1883_ = lean_box(0);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1883_);
v___x_1885_ = v___x_1877_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
v___jp_1888_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = l_Lake_InitTemplate_ctorIdx(v_tmp_1568_);
v___x_1896_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7, &l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
v___x_1897_ = lean_nat_dec_eq(v___x_1895_, v___x_1896_);
lean_dec(v___x_1895_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = 1;
lean_inc_n(v___y_1893_, 2);
v___x_1899_ = l_Lean_Name_toString(v___y_1893_, v___x_1898_);
v___x_1900_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1899_, v___y_1893_);
lean_dec_ref(v___x_1899_);
v___y_1867_ = v___y_1889_;
v___y_1868_ = v___y_1890_;
v___y_1869_ = v___y_1891_;
v___y_1870_ = v___y_1894_;
v___y_1871_ = v___y_1892_;
v___y_1872_ = v___y_1893_;
v___y_1873_ = v___x_1900_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1901_; 
lean_inc(v___y_1893_);
v___x_1901_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1893_);
v___y_1867_ = v___y_1889_;
v___y_1868_ = v___y_1890_;
v___y_1869_ = v___y_1891_;
v___y_1870_ = v___y_1894_;
v___y_1871_ = v___y_1892_;
v___y_1872_ = v___y_1893_;
v___y_1873_ = v___x_1901_;
goto v___jp_1866_;
}
}
v___jp_1902_:
{
if (v_a_1910_ == 0)
{
lean_object* v___x_1911_; 
v___x_1911_ = l_IO_FS_createDirAll(v___y_1908_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref_known(v___x_1911_, 1);
v___x_1912_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1913_ = l_IO_FS_writeFile(v___y_1903_, v___x_1912_);
lean_dec_ref(v___y_1903_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_dec_ref_known(v___x_1913_, 1);
v___y_1889_ = v___y_1904_;
v___y_1890_ = v___y_1905_;
v___y_1891_ = v___y_1906_;
v___y_1892_ = v___y_1907_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v_a_1565_;
goto v___jp_1888_;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1926_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1926_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1918_ = lean_io_error_to_string(v_a_1914_);
v___x_1919_ = 3;
v___x_1920_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*1, v___x_1919_);
lean_inc_ref(v_a_1565_);
v___x_1921_ = lean_apply_2(v_a_1565_, v___x_1920_, lean_box(0));
v___x_1922_ = lean_box(0);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1922_);
v___x_1924_ = v___x_1916_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1927_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1929_ = v___x_1911_;
v_isShared_1930_ = v_isSharedCheck_1939_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1911_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1939_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1931_ = lean_io_error_to_string(v_a_1927_);
v___x_1932_ = 3;
v___x_1933_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*1, v___x_1932_);
lean_inc_ref(v_a_1565_);
v___x_1934_ = lean_apply_2(v_a_1565_, v___x_1933_, lean_box(0));
v___x_1935_ = lean_box(0);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1935_);
v___x_1937_ = v___x_1929_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_dec_ref(v___y_1908_);
lean_dec_ref(v___y_1903_);
v___y_1889_ = v___y_1904_;
v___y_1890_ = v___y_1905_;
v___y_1891_ = v___y_1906_;
v___y_1892_ = v___y_1907_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v_a_1565_;
goto v___jp_1888_;
}
}
v___jp_1943_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_inc(v___y_1948_);
lean_inc(v___y_1947_);
lean_inc(v_name_1567_);
v___x_1949_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1568_, v_lang_1569_, v_name_1567_, v___y_1947_, v___y_1948_);
v___x_1950_ = l_IO_FS_writeFile(v_configFile_1942_, v___x_1949_);
lean_dec_ref(v___x_1949_);
lean_dec_ref(v_configFile_1942_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_dec_ref_known(v___x_1950_, 1);
if (lean_obj_tag(v___y_1946_) == 1)
{
lean_object* v_val_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_val_1951_ = lean_ctor_get(v___y_1946_, 0);
lean_inc_n(v_val_1951_, 2);
lean_dec_ref_known(v___y_1946_, 1);
v___x_1952_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1953_ = l_System_FilePath_withExtension(v_val_1951_, v___x_1952_);
v___x_1954_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_1953_);
v___x_1955_ = l_Lake_joinRelative(v___x_1953_, v___x_1954_);
v___x_1956_ = l_System_FilePath_pathExists(v___x_1955_);
v___x_1957_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1958_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1958_ == 0)
{
v___y_1903_ = v___x_1955_;
v___y_1904_ = v___y_1944_;
v___y_1905_ = v___y_1945_;
v___y_1906_ = v___y_1948_;
v___y_1907_ = v_val_1951_;
v___y_1908_ = v___x_1953_;
v___y_1909_ = v___y_1947_;
v_a_1910_ = v___x_1956_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1959_; size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1959_ = lean_box(0);
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1957_, v___x_1960_, v___x_1961_, v___x_1959_, v_a_1565_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_dec_ref_known(v___x_1962_, 1);
v___y_1903_ = v___x_1955_;
v___y_1904_ = v___y_1944_;
v___y_1905_ = v___y_1945_;
v___y_1906_ = v___y_1948_;
v___y_1907_ = v_val_1951_;
v___y_1908_ = v___x_1953_;
v___y_1909_ = v___y_1947_;
v_a_1910_ = v___x_1956_;
goto v___jp_1902_;
}
else
{
lean_dec_ref(v___x_1955_);
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1951_);
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_1962_;
}
}
}
else
{
lean_dec(v___y_1946_);
v___y_1861_ = v___y_1944_;
v___y_1862_ = v___y_1945_;
v___y_1863_ = v___y_1948_;
v___y_1864_ = v___y_1947_;
v___y_1865_ = v_a_1565_;
goto v___jp_1860_;
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_a_1963_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1965_ = v___x_1950_;
v_isShared_1966_ = v_isSharedCheck_1975_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1950_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1975_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1967_ = lean_io_error_to_string(v_a_1963_);
v___x_1968_ = 3;
v___x_1969_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*1, v___x_1968_);
lean_inc_ref(v_a_1565_);
v___x_1970_ = lean_apply_2(v_a_1565_, v___x_1969_, lean_box(0));
v___x_1971_ = lean_box(0);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1971_);
v___x_1973_ = v___x_1965_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
v___jp_1976_:
{
lean_object* v_lean_1979_; lean_object* v_toolchain_1980_; lean_object* v___x_1981_; 
v_lean_1979_ = lean_ctor_get(v_env_1570_, 1);
v_toolchain_1980_ = lean_ctor_get(v_env_1570_, 19);
lean_inc_ref(v_toolchain_1980_);
v___x_1981_ = l_Lake_ToolchainVer_ofString(v_toolchain_1980_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_ver_1982_; lean_object* v___x_1983_; 
v_ver_1982_ = lean_ctor_get(v___x_1981_, 1);
lean_inc_ref(v_ver_1982_);
lean_dec_ref_known(v___x_1981_, 2);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_ver_1982_);
lean_inc_ref(v_lean_1979_);
lean_inc_ref(v_toolchain_1980_);
v___y_1944_ = v_toolchain_1980_;
v___y_1945_ = v_lean_1979_;
v___y_1946_ = v_snd_1978_;
v___y_1947_ = v_fst_1977_;
v___y_1948_ = v___x_1983_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1984_; 
lean_dec_ref(v___x_1981_);
v___x_1984_ = lean_box(0);
lean_inc_ref(v_lean_1979_);
lean_inc_ref(v_toolchain_1980_);
v___y_1944_ = v_toolchain_1980_;
v___y_1945_ = v_lean_1979_;
v___y_1946_ = v_snd_1978_;
v___y_1947_ = v_fst_1977_;
v___y_1948_ = v___x_1984_;
goto v___jp_1943_;
}
}
v___jp_1985_:
{
if (v_a_1988_ == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1986_);
v_fst_1977_ = v___y_1987_;
v_snd_1978_ = v___x_1989_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_1990_; 
lean_dec_ref(v___y_1986_);
v___x_1990_ = lean_box(0);
v_fst_1977_ = v___y_1987_;
v_snd_1978_ = v___x_1990_;
goto v___jp_1976_;
}
}
v___jp_1991_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_box(0);
lean_inc(v_name_1567_);
v_fst_1977_ = v_name_1567_;
v_snd_1978_ = v___x_1992_;
goto v___jp_1976_;
}
v___jp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = l_Lake_InitTemplate_ctorIdx(v_tmp_1568_);
v___x_1997_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14);
v___x_1998_ = lean_nat_dec_eq(v___x_1996_, v___x_1997_);
lean_dec(v___x_1996_);
if (v___x_1998_ == 0)
{
if (v_a_1995_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
lean_inc(v_name_1567_);
v___x_1999_ = l_Lake_toUpperCamelCase(v_name_1567_);
lean_inc(v___x_1999_);
v___x_2000_ = l_Lean_modToFilePath(v_dir_1566_, v___x_1999_, v___y_1994_);
v___x_2001_ = l_System_FilePath_pathExists(v___x_2000_);
v___x_2002_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2003_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2003_ == 0)
{
v___y_1986_ = v___x_2000_;
v___y_1987_ = v___x_1999_;
v_a_1988_ = v___x_2001_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2004_; size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2002_, v___x_2005_, v___x_2006_, v___x_2004_, v_a_1565_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_dec_ref_known(v___x_2007_, 1);
v___y_1986_ = v___x_2000_;
v___y_1987_ = v___x_1999_;
v_a_1988_ = v___x_2001_;
goto v___jp_1985_;
}
else
{
lean_dec_ref(v___x_2000_);
lean_dec(v___x_1999_);
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_2007_;
}
}
}
else
{
goto v___jp_1991_;
}
}
else
{
goto v___jp_1991_;
}
}
v___jp_2008_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2009_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_1567_);
v___x_2010_ = l_Lean_modToFilePath(v_dir_1566_, v_name_1567_, v___x_2009_);
v___x_2011_ = l_System_FilePath_pathExists(v___x_2010_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2013_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2013_ == 0)
{
v___y_1994_ = v___x_2009_;
v_a_1995_ = v___x_2011_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2012_, v___x_2015_, v___x_2016_, v___x_2014_, v_a_1565_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref_known(v___x_2017_, 1);
v___y_1994_ = v___x_2009_;
v_a_1995_ = v___x_2011_;
goto v___jp_1993_;
}
else
{
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___x_2017_;
}
}
}
v___jp_2018_:
{
if (lean_obj_tag(v___y_2019_) == 0)
{
lean_dec_ref_known(v___y_2019_, 1);
goto v___jp_2008_;
}
else
{
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
return v___y_2019_;
}
}
v___jp_2021_:
{
if (v___x_2020_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1566_);
v___x_2024_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1566_, v_tmp_1568_, v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 1);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 2);
v___x_2026_ = lean_array_get_size(v_a_2025_);
v___x_2027_ = lean_nat_dec_lt(v___x_2022_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_a_2025_);
goto v___jp_2008_;
}
else
{
lean_object* v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = lean_usize_of_nat(v___x_2026_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2025_, v___x_2029_, v___x_2030_, v___x_2028_, v_a_1565_);
lean_dec(v_a_2025_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_dec_ref_known(v___x_2031_, 1);
goto v___jp_2008_;
}
else
{
v___y_2019_ = v___x_2031_;
goto v___jp_2018_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_a_2032_ = lean_ctor_get(v___x_2024_, 1);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2024_, 2);
v___x_2033_ = lean_array_get_size(v_a_2032_);
v___x_2034_ = lean_nat_dec_lt(v___x_2022_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_a_2032_);
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v___x_2035_ = lean_box(0);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = lean_usize_of_nat(v___x_2033_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2032_, v___x_2038_, v___x_2039_, v___x_2037_, v_a_1565_);
lean_dec(v_a_2032_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2040_, 0);
lean_dec(v_unused_2048_);
v___x_2042_ = v___x_2040_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v___x_2040_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 1);
lean_ctor_set(v___x_2042_, 0, v___x_2037_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2037_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
v___y_2019_ = v___x_2040_;
goto v___jp_2018_;
}
}
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_configFile_1942_);
lean_dec_ref(v_env_1570_);
lean_dec(v_name_1567_);
lean_dec_ref(v_dir_1566_);
v___x_2049_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
lean_inc_ref(v_a_1565_);
v___x_2050_ = lean_apply_2(v_a_1565_, v___x_2049_, lean_box(0));
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2059_, lean_object* v_dir_2060_, lean_object* v_name_2061_, lean_object* v_tmp_2062_, lean_object* v_lang_2063_, lean_object* v_env_2064_, lean_object* v_offline_2065_, lean_object* v_a_2066_){
_start:
{
uint8_t v_tmp_boxed_2067_; uint8_t v_lang_boxed_2068_; uint8_t v_offline_boxed_2069_; lean_object* v_res_2070_; 
v_tmp_boxed_2067_ = lean_unbox(v_tmp_2062_);
v_lang_boxed_2068_ = lean_unbox(v_lang_2063_);
v_offline_boxed_2069_ = lean_unbox(v_offline_2065_);
v_res_2070_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2059_, v_dir_2060_, v_name_2061_, v_tmp_boxed_2067_, v_lang_boxed_2068_, v_env_2064_, v_offline_boxed_2069_);
lean_dec_ref(v_a_2059_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* v_name_2072_, uint8_t v_tmp_2073_, uint8_t v_lang_2074_, lean_object* v_env_2075_, lean_object* v_cwd_2076_, uint8_t v_offline_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___y_2081_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v_a_2102_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2138_ = lean_string_dec_eq(v_name_2072_, v___x_2137_);
if (v___x_2138_ == 0)
{
v_a_2102_ = v_name_2072_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2139_; 
lean_dec_ref(v_name_2072_);
lean_inc_ref(v_cwd_2076_);
v___x_2139_ = lean_io_realpath(v_cwd_2076_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2157_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2157_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2157_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; 
lean_inc(v_a_2140_);
v___x_2144_ = l_System_FilePath_fileName(v_a_2140_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_dec_ref(v_cwd_2076_);
lean_dec_ref(v_env_2075_);
v___x_2145_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2146_ = lean_string_append(v___x_2145_, v_a_2140_);
lean_dec(v_a_2140_);
v___x_2147_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2148_ = lean_string_append(v___x_2146_, v___x_2147_);
v___x_2149_ = 3;
v___x_2150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set_uint8(v___x_2150_, sizeof(void*)*1, v___x_2149_);
lean_inc_ref(v_a_2078_);
v___x_2151_ = lean_apply_2(v_a_2078_, v___x_2150_, lean_box(0));
v___x_2152_ = lean_box(0);
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 1);
lean_ctor_set(v___x_2142_, 0, v___x_2152_);
v___x_2154_ = v___x_2142_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
else
{
lean_object* v_val_2156_; 
lean_del_object(v___x_2142_);
lean_dec(v_a_2140_);
v_val_2156_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_val_2156_);
lean_dec_ref_known(v___x_2144_, 1);
v_a_2102_ = v_val_2156_;
goto v___jp_2101_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v_cwd_2076_);
lean_dec_ref(v_env_2075_);
v_a_2158_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2160_ = v___x_2139_;
v_isShared_2161_ = v_isSharedCheck_2170_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2139_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2170_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2162_ = lean_io_error_to_string(v_a_2158_);
v___x_2163_ = 3;
v___x_2164_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*1, v___x_2163_);
lean_inc_ref(v_a_2078_);
v___x_2165_ = lean_apply_2(v_a_2078_, v___x_2164_, lean_box(0));
v___x_2166_ = lean_box(0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2166_);
v___x_2168_ = v___x_2160_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
v___jp_2080_:
{
lean_object* v___x_2082_; 
lean_inc_ref(v_cwd_2076_);
v___x_2082_ = l_IO_FS_createDirAll(v_cwd_2076_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref_known(v___x_2082_, 1);
v___x_2083_ = l_Lake_stringToLegalOrSimpleName(v___y_2081_);
v___x_2084_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2078_, v_cwd_2076_, v___x_2083_, v_tmp_2073_, v_lang_2074_, v_env_2075_, v_offline_2077_);
return v___x_2084_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v___y_2081_);
lean_dec_ref(v_cwd_2076_);
lean_dec_ref(v_env_2075_);
v_a_2085_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2087_ = v___x_2082_;
v_isShared_2088_ = v_isSharedCheck_2097_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2082_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2097_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2089_ = lean_io_error_to_string(v_a_2085_);
v___x_2090_ = 3;
v___x_2091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set_uint8(v___x_2091_, sizeof(void*)*1, v___x_2090_);
lean_inc_ref(v_a_2078_);
v___x_2092_ = lean_apply_2(v_a_2078_, v___x_2091_, lean_box(0));
v___x_2093_ = lean_box(0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2093_);
v___x_2095_ = v___x_2087_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
v___jp_2098_:
{
if (lean_obj_tag(v___y_2100_) == 0)
{
lean_dec_ref_known(v___y_2100_, 1);
v___y_2081_ = v___y_2099_;
goto v___jp_2080_;
}
else
{
lean_dec_ref(v___y_2099_);
lean_dec_ref(v_cwd_2076_);
lean_dec_ref(v_env_2075_);
return v___y_2100_;
}
}
v___jp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v_str_2107_; lean_object* v_startInclusive_2108_; lean_object* v_endExclusive_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = lean_string_utf8_byte_size(v_a_2102_);
v___x_2105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2105_, 0, v_a_2102_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v___x_2104_);
v___x_2106_ = l_String_Slice_trimAscii(v___x_2105_);
v_str_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_str_2107_);
v_startInclusive_2108_ = lean_ctor_get(v___x_2106_, 1);
lean_inc(v_startInclusive_2108_);
v_endExclusive_2109_ = lean_ctor_get(v___x_2106_, 2);
lean_inc(v_endExclusive_2109_);
lean_dec_ref(v___x_2106_);
v___x_2110_ = lean_string_utf8_extract_fast(v_str_2107_, v_startInclusive_2108_, v_endExclusive_2109_);
lean_dec(v_endExclusive_2109_);
lean_dec(v_startInclusive_2108_);
lean_dec_ref(v_str_2107_);
v___x_2111_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2110_);
v___x_2112_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2110_, v___x_2111_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 2);
v___x_2114_ = lean_array_get_size(v_a_2113_);
v___x_2115_ = lean_nat_dec_lt(v___x_2103_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec(v_a_2113_);
v___y_2081_ = v___x_2110_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = lean_usize_of_nat(v___x_2114_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2113_, v___x_2117_, v___x_2118_, v___x_2116_, v_a_2078_);
lean_dec(v_a_2113_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_dec_ref_known(v___x_2119_, 1);
v___y_2081_ = v___x_2110_;
goto v___jp_2080_;
}
else
{
v___y_2099_ = v___x_2110_;
v___y_2100_ = v___x_2119_;
goto v___jp_2098_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2112_, 2);
v___x_2121_ = lean_array_get_size(v_a_2120_);
v___x_2122_ = lean_nat_dec_lt(v___x_2103_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec(v_a_2120_);
lean_dec_ref(v___x_2110_);
lean_dec_ref(v_cwd_2076_);
lean_dec_ref(v_env_2075_);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
else
{
lean_object* v___x_2125_; size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = lean_box(0);
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = lean_usize_of_nat(v___x_2121_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2120_, v___x_2126_, v___x_2127_, v___x_2125_, v_a_2078_);
lean_dec(v_a_2120_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___x_2110_);
lean_dec_ref(v_cwd_2076_);
lean_dec_ref(v_env_2075_);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v___x_2128_, 0);
lean_dec(v_unused_2136_);
v___x_2130_ = v___x_2128_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_dec(v___x_2128_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 1);
lean_ctor_set(v___x_2130_, 0, v___x_2125_);
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2125_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
else
{
v___y_2099_ = v___x_2110_;
v___y_2100_ = v___x_2128_;
goto v___jp_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2171_, lean_object* v_tmp_2172_, lean_object* v_lang_2173_, lean_object* v_env_2174_, lean_object* v_cwd_2175_, lean_object* v_offline_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
uint8_t v_tmp_boxed_2179_; uint8_t v_lang_boxed_2180_; uint8_t v_offline_boxed_2181_; lean_object* v_res_2182_; 
v_tmp_boxed_2179_ = lean_unbox(v_tmp_2172_);
v_lang_boxed_2180_ = lean_unbox(v_lang_2173_);
v_offline_boxed_2181_ = lean_unbox(v_offline_2176_);
v_res_2182_ = l_Lake_init(v_name_2171_, v_tmp_boxed_2179_, v_lang_boxed_2180_, v_env_2174_, v_cwd_2175_, v_offline_boxed_2181_, v_a_2177_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* v_name_2183_, uint8_t v_tmp_2184_, uint8_t v_lang_2185_, lean_object* v_env_2186_, lean_object* v_cwd_2187_, uint8_t v_offline_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v_str_2195_; lean_object* v_startInclusive_2196_; lean_object* v_endExclusive_2197_; lean_object* v_name_2198_; lean_object* v___y_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_string_utf8_byte_size(v_name_2183_);
v___x_2193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2193_, 0, v_name_2183_);
lean_ctor_set(v___x_2193_, 1, v___x_2191_);
lean_ctor_set(v___x_2193_, 2, v___x_2192_);
v___x_2194_ = l_String_Slice_trimAscii(v___x_2193_);
v_str_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc_ref(v_str_2195_);
v_startInclusive_2196_ = lean_ctor_get(v___x_2194_, 1);
lean_inc(v_startInclusive_2196_);
v_endExclusive_2197_ = lean_ctor_get(v___x_2194_, 2);
lean_inc(v_endExclusive_2197_);
lean_dec_ref(v___x_2194_);
v_name_2198_ = lean_string_utf8_extract_fast(v_str_2195_, v_startInclusive_2196_, v_endExclusive_2197_);
lean_dec(v_endExclusive_2197_);
lean_dec(v_startInclusive_2196_);
lean_dec_ref(v_str_2195_);
v___x_2220_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2198_);
v___x_2221_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2198_, v___x_2220_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 2);
v___x_2223_ = lean_array_get_size(v_a_2222_);
v___x_2224_ = lean_nat_dec_lt(v___x_2191_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_dec(v_a_2222_);
goto v___jp_2199_;
}
else
{
lean_object* v___x_2225_; size_t v___x_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = lean_usize_of_nat(v___x_2223_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2222_, v___x_2226_, v___x_2227_, v___x_2225_, v_a_2189_);
lean_dec(v_a_2222_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_dec_ref_known(v___x_2228_, 1);
goto v___jp_2199_;
}
else
{
v___y_2219_ = v___x_2228_;
goto v___jp_2218_;
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v_a_2229_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2221_, 2);
v___x_2230_ = lean_array_get_size(v_a_2229_);
v___x_2231_ = lean_nat_dec_lt(v___x_2191_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v_a_2229_);
lean_dec_ref(v_name_2198_);
lean_dec_ref(v_cwd_2187_);
lean_dec_ref(v_env_2186_);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
else
{
lean_object* v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_box(0);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = lean_usize_of_nat(v___x_2230_);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2229_, v___x_2235_, v___x_2236_, v___x_2234_, v_a_2189_);
lean_dec(v_a_2229_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v_name_2198_);
lean_dec_ref(v_cwd_2187_);
lean_dec_ref(v_env_2186_);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2237_, 0);
lean_dec(v_unused_2245_);
v___x_2239_ = v___x_2237_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2237_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set_tag(v___x_2239_, 1);
lean_ctor_set(v___x_2239_, 0, v___x_2234_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2234_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
v___y_2219_ = v___x_2237_;
goto v___jp_2218_;
}
}
}
v___jp_2199_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = l_Lake_stringToLegalOrSimpleName(v_name_2198_);
lean_inc(v___x_2200_);
v___x_2201_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2200_);
v___x_2202_ = l_Lake_joinRelative(v_cwd_2187_, v___x_2201_);
lean_inc_ref(v___x_2202_);
v___x_2203_ = l_IO_FS_createDirAll(v___x_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2204_; 
lean_dec_ref_known(v___x_2203_, 1);
v___x_2204_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2189_, v___x_2202_, v___x_2200_, v_tmp_2184_, v_lang_2185_, v_env_2186_, v_offline_2188_);
return v___x_2204_;
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v___x_2202_);
lean_dec(v___x_2200_);
lean_dec_ref(v_env_2186_);
v_a_2205_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2207_ = v___x_2203_;
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2203_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2209_ = lean_io_error_to_string(v_a_2205_);
v___x_2210_ = 3;
v___x_2211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*1, v___x_2210_);
lean_inc_ref(v_a_2189_);
v___x_2212_ = lean_apply_2(v_a_2189_, v___x_2211_, lean_box(0));
v___x_2213_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2213_);
v___x_2215_ = v___x_2207_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
v___jp_2218_:
{
if (lean_obj_tag(v___y_2219_) == 0)
{
lean_dec_ref_known(v___y_2219_, 1);
goto v___jp_2199_;
}
else
{
lean_dec_ref(v_name_2198_);
lean_dec_ref(v_cwd_2187_);
lean_dec_ref(v_env_2186_);
return v___y_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2246_, lean_object* v_tmp_2247_, lean_object* v_lang_2248_, lean_object* v_env_2249_, lean_object* v_cwd_2250_, lean_object* v_offline_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
uint8_t v_tmp_boxed_2254_; uint8_t v_lang_boxed_2255_; uint8_t v_offline_boxed_2256_; lean_object* v_res_2257_; 
v_tmp_boxed_2254_ = lean_unbox(v_tmp_2247_);
v_lang_boxed_2255_ = lean_unbox(v_lang_2248_);
v_offline_boxed_2256_ = lean_unbox(v_offline_2251_);
v_res_2257_ = l_Lake_new(v_name_2246_, v_tmp_boxed_2254_, v_lang_boxed_2255_, v_env_2249_, v_cwd_2250_, v_offline_boxed_2256_, v_a_2252_);
lean_dec_ref(v_a_2252_);
return v_res_2257_;
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
