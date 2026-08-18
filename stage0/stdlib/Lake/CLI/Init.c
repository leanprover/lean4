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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "update.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "create-release.yml"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "created Mathlib update CI workflow at '"};
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
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to initialize git repository"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "README.md"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "illegal package name '"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lake"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value),((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "reserved package name"};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10 = (const lean_object*)&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_289__boxed_499_; lean_object* v_res_500_; 
v_x_289__boxed_499_ = lean_unbox(v_x_497_);
v_res_500_ = l_Lake_instReprInitTemplate_repr(v_x_289__boxed_499_, v_prec_498_);
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
uint8_t v_x_13__boxed_527_; uint8_t v_y_14__boxed_528_; uint8_t v_res_529_; lean_object* v_r_530_; 
v_x_13__boxed_527_ = lean_unbox(v_x_525_);
v_y_14__boxed_528_ = lean_unbox(v_y_526_);
v_res_529_ = l_Lake_instDecidableEqInitTemplate(v_x_13__boxed_527_, v_y_14__boxed_528_);
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
uint32_t v___y_623_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_string_utf8_byte_size(v_s_620_);
v___x_629_ = lean_nat_dec_eq(v_p_621_, v___x_628_);
if (v___x_629_ == 0)
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
uint32_t v___y_642_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_string_utf8_byte_size(v_s_639_);
v___x_648_ = lean_nat_dec_eq(v_p_640_, v___x_647_);
if (v___x_648_ == 0)
{
uint32_t v___x_649_; uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_string_utf8_get_fast(v_s_639_, v_p_640_);
v___x_650_ = 65;
v___x_651_ = lean_uint32_dec_le(v___x_650_, v___x_649_);
if (v___x_651_ == 0)
{
v___y_642_ = v___x_649_;
goto v___jp_641_;
}
else
{
uint32_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 90;
v___x_653_ = lean_uint32_dec_le(v___x_649_, v___x_652_);
if (v___x_653_ == 0)
{
v___y_642_ = v___x_649_;
goto v___jp_641_;
}
else
{
uint32_t v___x_654_; uint32_t v___x_655_; 
v___x_654_ = 32;
v___x_655_ = lean_uint32_add(v___x_649_, v___x_654_);
v___y_642_ = v___x_655_;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t v_tmp_658_, uint8_t v_lang_659_, lean_object* v_pkgName_660_, lean_object* v_root_661_, lean_object* v_leanVer_x3f_662_){
_start:
{
lean_object* v_pkgNameStr_663_; lean_object* v___y_665_; 
v_pkgNameStr_663_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_660_);
if (lean_obj_tag(v_leanVer_x3f_662_) == 0)
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___y_665_ = v___x_696_;
goto v___jp_664_;
}
else
{
lean_object* v_val_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_val_697_ = lean_ctor_get(v_leanVer_x3f_662_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v_leanVer_x3f_662_, 1);
v___x_698_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1));
v___x_699_ = l_Lake_StdVer_toString(v_val_697_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
v___y_665_ = v___x_700_;
goto v___jp_664_;
}
v___jp_664_:
{
switch(v_tmp_658_)
{
case 0:
{
lean_dec_ref(v___y_665_);
if (v_lang_659_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_661_);
lean_dec(v_root_661_);
v___x_667_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_663_);
v___x_668_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_663_, v___x_667_);
v___x_669_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(v_pkgNameStr_663_, v___x_666_, v___x_668_);
lean_dec_ref(v___x_666_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_670_ = 1;
v___x_671_ = l_Lean_Name_toString(v_root_661_, v___x_670_);
v___x_672_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_663_);
v___x_673_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_663_, v___x_672_);
v___x_674_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(v_pkgNameStr_663_, v___x_671_, v___x_673_);
return v___x_674_;
}
}
case 1:
{
lean_dec_ref(v___y_665_);
lean_dec(v_root_661_);
if (v_lang_659_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_663_);
v___x_676_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_663_, v___x_675_);
v___x_677_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(v_pkgNameStr_663_, v___x_676_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_pkgNameStr_663_);
v___x_679_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_663_, v___x_678_);
v___x_680_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(v_pkgNameStr_663_, v___x_679_);
return v___x_680_;
}
}
case 2:
{
lean_dec_ref(v___y_665_);
if (v_lang_659_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_661_);
lean_dec(v_root_661_);
v___x_682_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(v_pkgNameStr_663_, v___x_681_);
lean_dec_ref(v___x_681_);
return v___x_682_;
}
else
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = 1;
v___x_684_ = l_Lean_Name_toString(v_root_661_, v___x_683_);
v___x_685_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(v_pkgNameStr_663_, v___x_684_);
return v___x_685_;
}
}
case 3:
{
if (v_lang_659_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_661_);
lean_dec(v_root_661_);
v___x_687_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(v_pkgNameStr_663_, v___x_686_, v___y_665_);
lean_dec_ref(v___x_686_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = 1;
v___x_689_ = l_Lean_Name_toString(v_root_661_, v___x_688_);
v___x_690_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(v_pkgNameStr_663_, v___x_689_, v___y_665_);
return v___x_690_;
}
}
default: 
{
if (v_lang_659_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_661_);
lean_dec(v_root_661_);
v___x_692_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(v_pkgNameStr_663_, v___x_691_, v___y_665_);
lean_dec_ref(v___x_691_);
return v___x_692_;
}
else
{
uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = 1;
v___x_694_ = l_Lean_Name_toString(v_root_661_, v___x_693_);
v___x_695_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(v_pkgNameStr_663_, v___x_694_, v___y_665_);
return v___x_695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* v_tmp_701_, lean_object* v_lang_702_, lean_object* v_pkgName_703_, lean_object* v_root_704_, lean_object* v_leanVer_x3f_705_){
_start:
{
uint8_t v_tmp_boxed_706_; uint8_t v_lang_boxed_707_; lean_object* v_res_708_; 
v_tmp_boxed_706_ = lean_unbox(v_tmp_701_);
v_lang_boxed_707_ = lean_unbox(v_lang_702_);
v_res_708_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_boxed_706_, v_lang_boxed_707_, v_pkgName_703_, v_root_704_, v_leanVer_x3f_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* v_dir_734_, uint8_t v_tmp_735_, lean_object* v_a_736_){
_start:
{
uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_738_ = 0;
v___x_739_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1));
v___x_740_ = lean_array_push(v_a_736_, v___x_739_);
v___x_741_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2));
v___x_742_ = l_Lake_joinRelative(v_dir_734_, v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3));
v___x_744_ = l_Lake_joinRelative(v___x_742_, v___x_743_);
lean_inc_ref(v___x_744_);
v___x_745_ = l_IO_FS_createDirAll(v___x_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___y_749_; uint8_t v___x_804_; 
lean_dec_ref_known(v___x_745_, 1);
v___x_746_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4));
lean_inc_ref(v___x_744_);
v___x_747_ = l_Lake_joinRelative(v___x_744_, v___x_746_);
v___x_804_ = l_System_FilePath_pathExists(v___x_747_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; uint8_t v___x_806_; 
v___x_805_ = 4;
v___x_806_ = l_Lake_instDecidableEqInitTemplate(v_tmp_735_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0));
v___x_808_ = l_IO_FS_writeFile(v___x_747_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_dec_ref_known(v___x_808_, 1);
v___y_749_ = v___x_740_;
goto v___jp_748_;
}
else
{
lean_object* v_a_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = lean_io_error_to_string(v_a_809_);
v___x_811_ = 3;
v___x_812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*1, v___x_811_);
v___x_813_ = lean_array_get_size(v___x_740_);
v___x_814_ = lean_array_push(v___x_740_, v___x_812_);
v___x_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
return v___x_815_;
}
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0));
v___x_817_ = l_IO_FS_writeFile(v___x_747_, v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref_known(v___x_817_, 1);
v___y_749_ = v___x_740_;
goto v___jp_748_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = lean_io_error_to_string(v_a_818_);
v___x_820_ = 3;
v___x_821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v___x_820_);
v___x_822_ = lean_array_get_size(v___x_740_);
v___x_823_ = lean_array_push(v___x_740_, v___x_821_);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
return v___x_824_;
}
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
v___x_825_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16));
v___x_826_ = lean_array_push(v___x_740_, v___x_825_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
return v___x_828_;
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; 
v___x_750_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5));
v___x_751_ = lean_string_append(v___x_750_, v___x_747_);
lean_dec_ref(v___x_747_);
v___x_752_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*1, v___x_738_);
v___x_755_ = lean_array_push(v___y_749_, v___x_754_);
v___x_756_ = 4;
v___x_757_ = l_Lake_instDecidableEqInitTemplate(v_tmp_735_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v___x_744_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_755_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7));
lean_inc_ref(v___x_744_);
v___x_761_ = l_Lake_joinRelative(v___x_744_, v___x_760_);
v___x_762_ = l_System_FilePath_pathExists(v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0));
v___x_764_ = l_IO_FS_writeFile(v___x_761_, v___x_763_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref_known(v___x_764_, 1);
v___x_765_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8));
v___x_766_ = l_Lake_joinRelative(v___x_744_, v___x_765_);
v___x_767_ = l_System_FilePath_pathExists(v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9));
v___x_769_ = lean_string_append(v___x_768_, v___x_761_);
lean_dec_ref(v___x_761_);
v___x_770_ = lean_string_append(v___x_769_, v___x_752_);
v___x_771_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*1, v___x_738_);
v___x_772_ = lean_array_push(v___x_755_, v___x_771_);
if (v___x_767_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0));
v___x_774_ = l_IO_FS_writeFile(v___x_766_, v___x_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref_known(v___x_774_, 1);
v___x_775_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10));
v___x_776_ = lean_string_append(v___x_775_, v___x_766_);
lean_dec_ref(v___x_766_);
v___x_777_ = lean_string_append(v___x_776_, v___x_752_);
v___x_778_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_778_, sizeof(void*)*1, v___x_738_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_array_push(v___x_772_, v___x_778_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
return v___x_781_;
}
else
{
lean_object* v_a_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v___x_766_);
v_a_782_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_774_, 1);
v___x_783_ = lean_io_error_to_string(v_a_782_);
v___x_784_ = 3;
v___x_785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___x_786_ = lean_array_get_size(v___x_772_);
v___x_787_ = lean_array_push(v___x_772_, v___x_785_);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
return v___x_788_;
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v___x_766_);
v___x_789_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12));
v___x_790_ = lean_array_push(v___x_772_, v___x_789_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
return v___x_792_;
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v___x_761_);
lean_dec_ref(v___x_744_);
v_a_793_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_764_, 1);
v___x_794_ = lean_io_error_to_string(v_a_793_);
v___x_795_ = 3;
v___x_796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*1, v___x_795_);
v___x_797_ = lean_array_get_size(v___x_755_);
v___x_798_ = lean_array_push(v___x_755_, v___x_796_);
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
return v___x_799_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v___x_761_);
lean_dec_ref(v___x_744_);
v___x_800_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14));
v___x_801_ = lean_array_push(v___x_755_, v___x_800_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v___x_744_);
v_a_829_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_745_, 1);
v___x_830_ = lean_io_error_to_string(v_a_829_);
v___x_831_ = 3;
v___x_832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*1, v___x_831_);
v___x_833_ = lean_array_get_size(v___x_740_);
v___x_834_ = lean_array_push(v___x_740_, v___x_832_);
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* v_dir_836_, lean_object* v_tmp_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
uint8_t v_tmp_boxed_840_; lean_object* v_res_841_; 
v_tmp_boxed_840_ = lean_unbox(v_tmp_837_);
v_res_841_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_836_, v_tmp_boxed_840_, v_a_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* v_as_842_, size_t v_i_843_, size_t v_stop_844_, lean_object* v_b_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_eq(v_i_843_, v_stop_844_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; 
v___x_849_ = lean_array_uget_borrowed(v_as_842_, v_i_843_);
lean_inc_ref(v___y_846_);
lean_inc(v___x_849_);
v___x_850_ = lean_apply_2(v___y_846_, v___x_849_, lean_box(0));
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_843_, v___x_851_);
v_i_843_ = v___x_852_;
v_b_845_ = v___x_850_;
goto _start;
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_845_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
size_t v_i_boxed_861_; size_t v_stop_boxed_862_; lean_object* v_res_863_; 
v_i_boxed_861_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_862_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_855_, v_i_boxed_861_, v_stop_boxed_862_, v_b_858_, v___y_859_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_as_855_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_878_ = lean_array_get_size(v___x_877_);
return v___x_878_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_nat_dec_lt(v___x_880_, v___x_879_);
return v___x_881_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9(void){
_start:
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_883_ = lean_nat_dec_le(v___x_882_, v___x_882_);
return v___x_883_;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10(void){
_start:
{
lean_object* v___x_884_; size_t v___x_885_; 
v___x_884_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
v___x_885_ = lean_usize_of_nat(v___x_884_);
return v___x_885_;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0));
v___x_891_ = l_Lake_Git_upstreamBranch;
v___x_892_ = lean_string_dec_eq(v___x_891_, v___x_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* v_dir_900_, lean_object* v_name_901_, uint8_t v_tmp_902_, uint8_t v_lang_903_, lean_object* v_env_904_, uint8_t v_offline_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_911_; lean_object* v___y_913_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_941_; lean_object* v___y_942_; uint8_t v_a_943_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v_a_1075_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v_a_1144_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; uint8_t v_a_1176_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; uint8_t v_a_1277_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_configFile_1309_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___y_1357_; lean_object* v___y_1358_; uint8_t v_a_1359_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1380_; uint8_t v_a_1381_; lean_object* v___y_1399_; uint8_t v___x_1400_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_911_ = l_Lake_defaultConfigFile;
v___x_1307_ = l_Lake_ConfigLang_fileExtension(v_lang_903_);
v___x_1308_ = l_System_FilePath_addExtension(v___x_911_, v___x_1307_);
lean_dec_ref(v___x_1307_);
lean_inc_ref(v_dir_900_);
v_configFile_1309_ = l_Lake_joinRelative(v_dir_900_, v___x_1308_);
v___x_1400_ = l_System_FilePath_pathExists(v_configFile_1309_);
v___x_1433_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1434_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1434_ == 0)
{
goto v___jp_1401_;
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1436_ == 0)
{
if (v___x_1434_ == 0)
{
goto v___jp_1401_;
}
else
{
size_t v___x_1437_; size_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1433_, v___x_1437_, v___x_1438_, v___x_1435_, v_a_906_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref_known(v___x_1439_, 1);
goto v___jp_1401_;
}
else
{
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1439_;
}
}
}
else
{
size_t v___x_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = ((size_t)0ULL);
v___x_1441_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1433_, v___x_1440_, v___x_1441_, v___x_1435_, v_a_906_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref_known(v___x_1442_, 1);
goto v___jp_1401_;
}
else
{
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1442_;
}
}
}
v___jp_908_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
v___jp_912_:
{
if (v_offline_905_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_914_ = lean_box(0);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_box(0);
v___x_917_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_900_);
v___x_918_ = l_Lake_joinRelative(v_dir_900_, v___x_917_);
lean_inc_ref(v___x_918_);
v___x_919_ = l_Lake_joinRelative(v___x_918_, v___x_911_);
v___x_920_ = l_Lake_defaultManifestFile;
v___x_921_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_922_ = lean_box(1);
v___x_923_ = l_Lean_Options_empty;
v___x_924_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_925_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_925_, 0, v_env_904_);
lean_ctor_set(v___x_925_, 1, v___x_914_);
lean_ctor_set(v___x_925_, 2, v_dir_900_);
lean_ctor_set(v___x_925_, 3, v___x_915_);
lean_ctor_set(v___x_925_, 4, v___x_916_);
lean_ctor_set(v___x_925_, 5, v___x_917_);
lean_ctor_set(v___x_925_, 6, v___x_918_);
lean_ctor_set(v___x_925_, 7, v___x_911_);
lean_ctor_set(v___x_925_, 8, v___x_919_);
lean_ctor_set(v___x_925_, 9, v___x_914_);
lean_ctor_set(v___x_925_, 10, v___x_920_);
lean_ctor_set(v___x_925_, 11, v___x_921_);
lean_ctor_set(v___x_925_, 12, v___x_922_);
lean_ctor_set(v___x_925_, 13, v___x_923_);
lean_ctor_set(v___x_925_, 14, v___x_924_);
lean_ctor_set(v___x_925_, 15, v___x_924_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*16, v_offline_905_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*16 + 1, v_offline_905_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*16 + 2, v_offline_905_);
v___x_926_ = l_Lean_NameSet_empty;
v___x_927_ = l_Lake_updateManifest(v___x_925_, v___x_926_, v___y_913_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
v___jp_930_:
{
if (lean_obj_tag(v___y_931_) == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_932_);
v___x_934_ = lean_apply_2(v___y_932_, v___x_933_, lean_box(0));
v___y_913_ = v___y_932_;
goto v___jp_912_;
}
else
{
lean_dec_ref_known(v___y_931_, 1);
v___y_913_ = v___y_932_;
goto v___jp_912_;
}
}
v___jp_935_:
{
switch(v_tmp_902_)
{
case 3:
{
v___y_931_ = v___y_936_;
v___y_932_ = v___y_937_;
goto v___jp_930_;
}
case 4:
{
v___y_931_ = v___y_936_;
v___y_932_ = v___y_937_;
goto v___jp_930_;
}
default: 
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v___y_936_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
}
v___jp_940_:
{
if (v_a_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_942_);
v___x_945_ = lean_apply_2(v___y_942_, v___x_944_, lean_box(0));
v___y_936_ = v___y_941_;
v___y_937_ = v___y_942_;
goto v___jp_935_;
}
else
{
v___y_936_ = v___y_941_;
v___y_937_ = v___y_942_;
goto v___jp_935_;
}
}
v___jp_946_:
{
lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; 
v___x_951_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_900_);
v___x_952_ = l_Lake_joinRelative(v_dir_900_, v___x_951_);
v___x_953_ = 4;
v___x_954_ = lean_io_prim_handle_mk(v___x_952_, v___x_953_);
lean_dec_ref(v___x_952_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_957_ = lean_io_prim_handle_put_str(v_a_955_, v___x_956_);
lean_dec(v_a_955_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
lean_dec_ref_known(v___x_957_, 1);
v___x_958_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_900_);
v___x_959_ = l_Lake_joinRelative(v_dir_900_, v___x_958_);
v___x_960_ = lean_string_utf8_byte_size(v___y_948_);
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_nat_dec_eq(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec_ref(v___y_947_);
v___x_963_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_964_ = lean_string_append(v___y_948_, v___x_963_);
v___x_965_ = l_IO_FS_writeFile(v___x_959_, v___x_964_);
lean_dec_ref(v___x_964_);
lean_dec_ref(v___x_959_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_dec_ref_known(v___x_965_, 1);
v___y_936_ = v___y_949_;
v___y_937_ = v___y_950_;
goto v___jp_935_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_978_; 
lean_dec(v___y_949_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_970_ = lean_io_error_to_string(v_a_966_);
v___x_971_ = 3;
v___x_972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_971_);
lean_inc_ref(v___y_950_);
v___x_973_ = lean_apply_2(v___y_950_, v___x_972_, lean_box(0));
v___x_974_ = lean_box(0);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_974_);
v___x_976_ = v___x_968_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_githash_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
lean_dec_ref(v___y_948_);
v_githash_979_ = lean_ctor_get(v___y_947_, 1);
lean_inc_ref(v_githash_979_);
lean_dec_ref(v___y_947_);
v___x_980_ = lean_string_utf8_byte_size(v_githash_979_);
lean_dec_ref(v_githash_979_);
v___x_981_ = lean_nat_dec_eq(v___x_980_, v___x_961_);
if (v___x_981_ == 0)
{
uint8_t v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = l_System_FilePath_pathExists(v___x_959_);
lean_dec_ref(v___x_959_);
v___x_983_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_984_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_984_ == 0)
{
v___y_941_ = v___y_949_;
v___y_942_ = v___y_950_;
v_a_943_ = v___x_982_;
goto v___jp_940_;
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = lean_box(0);
v___x_986_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_986_ == 0)
{
if (v___x_984_ == 0)
{
v___y_941_ = v___y_949_;
v___y_942_ = v___y_950_;
v_a_943_ = v___x_982_;
goto v___jp_940_;
}
else
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((size_t)0ULL);
v___x_988_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_983_, v___x_987_, v___x_988_, v___x_985_, v___y_950_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_dec_ref_known(v___x_989_, 1);
v___y_941_ = v___y_949_;
v___y_942_ = v___y_950_;
v_a_943_ = v___x_982_;
goto v___jp_940_;
}
else
{
lean_dec(v___y_949_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
return v___x_989_;
}
}
}
else
{
size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_990_ = ((size_t)0ULL);
v___x_991_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_983_, v___x_990_, v___x_991_, v___x_985_, v___y_950_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_dec_ref_known(v___x_992_, 1);
v___y_941_ = v___y_949_;
v___y_942_ = v___y_950_;
v_a_943_ = v___x_982_;
goto v___jp_940_;
}
else
{
lean_dec(v___y_949_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
return v___x_992_;
}
}
}
}
else
{
lean_dec_ref(v___x_959_);
v___y_936_ = v___y_949_;
v___y_937_ = v___y_950_;
goto v___jp_935_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
v_a_993_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_995_ = v___x_957_;
v_isShared_996_ = v_isSharedCheck_1005_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_957_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1005_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_997_ = lean_io_error_to_string(v_a_993_);
v___x_998_ = 3;
v___x_999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_998_);
lean_inc_ref(v___y_950_);
v___x_1000_ = lean_apply_2(v___y_950_, v___x_999_, lean_box(0));
v___x_1001_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1001_);
v___x_1003_ = v___x_995_;
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
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
v_a_1006_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1008_ = v___x_954_;
v_isShared_1009_ = v_isSharedCheck_1018_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_954_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1018_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1010_ = lean_io_error_to_string(v_a_1006_);
v___x_1011_ = 3;
v___x_1012_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_1011_);
lean_inc_ref(v___y_950_);
v___x_1013_ = lean_apply_2(v___y_950_, v___x_1012_, lean_box(0));
v___x_1014_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1014_);
v___x_1016_ = v___x_1008_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
v___jp_1019_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(v___y_1021_);
v___x_1025_ = lean_apply_2(v___y_1021_, v___x_1024_, lean_box(0));
v___y_947_ = v___y_1020_;
v___y_948_ = v___y_1022_;
v___y_949_ = v___y_1023_;
v___y_950_ = v___y_1021_;
goto v___jp_946_;
}
v___jp_1026_:
{
if (lean_obj_tag(v___y_1031_) == 0)
{
lean_dec_ref_known(v___y_1031_, 1);
v___y_947_ = v___y_1027_;
v___y_948_ = v___y_1029_;
v___y_949_ = v___y_1030_;
v___y_950_ = v___y_1028_;
goto v___jp_946_;
}
else
{
lean_dec_ref_known(v___y_1031_, 1);
v___y_1020_ = v___y_1027_;
v___y_1021_ = v___y_1028_;
v___y_1022_ = v___y_1029_;
v___y_1023_ = v___y_1030_;
goto v___jp_1019_;
}
}
v___jp_1032_:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = l_Lake_Git_upstreamBranch;
v___x_1038_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_900_);
v___x_1041_ = l_Lake_GitRepo_checkoutBranch(v___x_1037_, v_dir_900_, v___x_1040_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 2);
v___x_1043_ = lean_array_get_size(v_a_1042_);
v___x_1044_ = lean_nat_dec_lt(v___x_1039_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec(v_a_1042_);
v___y_947_ = v___y_1033_;
v___y_948_ = v___y_1035_;
v___y_949_ = v___y_1036_;
v___y_950_ = v___y_1034_;
goto v___jp_946_;
}
else
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_nat_dec_le(v___x_1043_, v___x_1043_);
if (v___x_1046_ == 0)
{
if (v___x_1044_ == 0)
{
lean_dec(v_a_1042_);
v___y_947_ = v___y_1033_;
v___y_948_ = v___y_1035_;
v___y_949_ = v___y_1036_;
v___y_950_ = v___y_1034_;
goto v___jp_946_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = lean_usize_of_nat(v___x_1043_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1042_, v___x_1047_, v___x_1048_, v___x_1045_, v___y_1034_);
lean_dec(v_a_1042_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_dec_ref_known(v___x_1049_, 1);
v___y_947_ = v___y_1033_;
v___y_948_ = v___y_1035_;
v___y_949_ = v___y_1036_;
v___y_950_ = v___y_1034_;
goto v___jp_946_;
}
else
{
v___y_1027_ = v___y_1033_;
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___y_1035_;
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1049_;
goto v___jp_1026_;
}
}
}
else
{
size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = ((size_t)0ULL);
v___x_1051_ = lean_usize_of_nat(v___x_1043_);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1042_, v___x_1050_, v___x_1051_, v___x_1045_, v___y_1034_);
lean_dec(v_a_1042_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_dec_ref_known(v___x_1052_, 1);
v___y_947_ = v___y_1033_;
v___y_948_ = v___y_1035_;
v___y_949_ = v___y_1036_;
v___y_950_ = v___y_1034_;
goto v___jp_946_;
}
else
{
v___y_1027_ = v___y_1033_;
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___y_1035_;
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1052_;
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1041_, 2);
v___x_1054_ = lean_array_get_size(v_a_1053_);
v___x_1055_ = lean_nat_dec_lt(v___x_1039_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec(v_a_1053_);
v___y_1020_ = v___y_1033_;
v___y_1021_ = v___y_1034_;
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_nat_dec_le(v___x_1054_, v___x_1054_);
if (v___x_1057_ == 0)
{
if (v___x_1055_ == 0)
{
lean_dec(v_a_1053_);
v___y_1020_ = v___y_1033_;
v___y_1021_ = v___y_1034_;
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1019_;
}
else
{
size_t v___x_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = lean_usize_of_nat(v___x_1054_);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1053_, v___x_1058_, v___x_1059_, v___x_1056_, v___y_1034_);
lean_dec(v_a_1053_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_dec_ref_known(v___x_1060_, 1);
v___y_1020_ = v___y_1033_;
v___y_1021_ = v___y_1034_;
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1019_;
}
else
{
v___y_1027_ = v___y_1033_;
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___y_1035_;
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1060_;
goto v___jp_1026_;
}
}
}
else
{
size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = lean_usize_of_nat(v___x_1054_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1053_, v___x_1061_, v___x_1062_, v___x_1056_, v___y_1034_);
lean_dec(v_a_1053_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_dec_ref_known(v___x_1063_, 1);
v___y_1020_ = v___y_1033_;
v___y_1021_ = v___y_1034_;
v___y_1022_ = v___y_1035_;
v___y_1023_ = v___y_1036_;
goto v___jp_1019_;
}
else
{
v___y_1027_ = v___y_1033_;
v___y_1028_ = v___y_1034_;
v___y_1029_ = v___y_1035_;
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1063_;
goto v___jp_1026_;
}
}
}
}
}
else
{
v___y_947_ = v___y_1033_;
v___y_948_ = v___y_1035_;
v___y_949_ = v___y_1036_;
v___y_950_ = v___y_1034_;
goto v___jp_946_;
}
}
v___jp_1064_:
{
if (lean_obj_tag(v___y_1069_) == 0)
{
lean_dec_ref_known(v___y_1069_, 1);
v___y_1033_ = v___y_1065_;
v___y_1034_ = v___y_1066_;
v___y_1035_ = v___y_1067_;
v___y_1036_ = v___y_1068_;
goto v___jp_1032_;
}
else
{
lean_dec_ref_known(v___y_1069_, 1);
v___y_1020_ = v___y_1065_;
v___y_1021_ = v___y_1066_;
v___y_1022_ = v___y_1067_;
v___y_1023_ = v___y_1068_;
goto v___jp_1019_;
}
}
v___jp_1070_:
{
if (v_a_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_900_);
v___x_1078_ = l_Lake_GitRepo_quietInit(v_dir_900_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 2);
v___x_1080_ = lean_array_get_size(v_a_1079_);
v___x_1081_ = lean_nat_dec_lt(v___x_1076_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_dec(v_a_1079_);
v___y_1033_ = v___y_1071_;
v___y_1034_ = v___y_1072_;
v___y_1035_ = v___y_1073_;
v___y_1036_ = v___y_1074_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_nat_dec_le(v___x_1080_, v___x_1080_);
if (v___x_1083_ == 0)
{
if (v___x_1081_ == 0)
{
lean_dec(v_a_1079_);
v___y_1033_ = v___y_1071_;
v___y_1034_ = v___y_1072_;
v___y_1035_ = v___y_1073_;
v___y_1036_ = v___y_1074_;
goto v___jp_1032_;
}
else
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1080_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1079_, v___x_1084_, v___x_1085_, v___x_1082_, v___y_1072_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_dec_ref_known(v___x_1086_, 1);
v___y_1033_ = v___y_1071_;
v___y_1034_ = v___y_1072_;
v___y_1035_ = v___y_1073_;
v___y_1036_ = v___y_1074_;
goto v___jp_1032_;
}
else
{
v___y_1065_ = v___y_1071_;
v___y_1066_ = v___y_1072_;
v___y_1067_ = v___y_1073_;
v___y_1068_ = v___y_1074_;
v___y_1069_ = v___x_1086_;
goto v___jp_1064_;
}
}
}
else
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1080_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1079_, v___x_1087_, v___x_1088_, v___x_1082_, v___y_1072_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_dec_ref_known(v___x_1089_, 1);
v___y_1033_ = v___y_1071_;
v___y_1034_ = v___y_1072_;
v___y_1035_ = v___y_1073_;
v___y_1036_ = v___y_1074_;
goto v___jp_1032_;
}
else
{
v___y_1065_ = v___y_1071_;
v___y_1066_ = v___y_1072_;
v___y_1067_ = v___y_1073_;
v___y_1068_ = v___y_1074_;
v___y_1069_ = v___x_1089_;
goto v___jp_1064_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_a_1090_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1078_, 2);
v___x_1091_ = lean_array_get_size(v_a_1090_);
v___x_1092_ = lean_nat_dec_lt(v___x_1076_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec(v_a_1090_);
v___y_1020_ = v___y_1071_;
v___y_1021_ = v___y_1072_;
v___y_1022_ = v___y_1073_;
v___y_1023_ = v___y_1074_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_nat_dec_le(v___x_1091_, v___x_1091_);
if (v___x_1094_ == 0)
{
if (v___x_1092_ == 0)
{
lean_dec(v_a_1090_);
v___y_1020_ = v___y_1071_;
v___y_1021_ = v___y_1072_;
v___y_1022_ = v___y_1073_;
v___y_1023_ = v___y_1074_;
goto v___jp_1019_;
}
else
{
size_t v___x_1095_; size_t v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = lean_usize_of_nat(v___x_1091_);
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1090_, v___x_1095_, v___x_1096_, v___x_1093_, v___y_1072_);
lean_dec(v_a_1090_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_dec_ref_known(v___x_1097_, 1);
v___y_1020_ = v___y_1071_;
v___y_1021_ = v___y_1072_;
v___y_1022_ = v___y_1073_;
v___y_1023_ = v___y_1074_;
goto v___jp_1019_;
}
else
{
v___y_1065_ = v___y_1071_;
v___y_1066_ = v___y_1072_;
v___y_1067_ = v___y_1073_;
v___y_1068_ = v___y_1074_;
v___y_1069_ = v___x_1097_;
goto v___jp_1064_;
}
}
}
else
{
size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = lean_usize_of_nat(v___x_1091_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1090_, v___x_1098_, v___x_1099_, v___x_1093_, v___y_1072_);
lean_dec(v_a_1090_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref_known(v___x_1100_, 1);
v___y_1020_ = v___y_1071_;
v___y_1021_ = v___y_1072_;
v___y_1022_ = v___y_1073_;
v___y_1023_ = v___y_1074_;
goto v___jp_1019_;
}
else
{
v___y_1065_ = v___y_1071_;
v___y_1066_ = v___y_1072_;
v___y_1067_ = v___y_1073_;
v___y_1068_ = v___y_1074_;
v___y_1069_ = v___x_1100_;
goto v___jp_1064_;
}
}
}
}
}
else
{
v___y_947_ = v___y_1071_;
v___y_948_ = v___y_1073_;
v___y_949_ = v___y_1074_;
v___y_950_ = v___y_1072_;
goto v___jp_946_;
}
}
v___jp_1101_:
{
uint8_t v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
lean_inc_ref(v_dir_900_);
v___x_1106_ = l_Lake_GitRepo_insideWorkTree(v_dir_900_);
v___x_1107_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1108_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1108_ == 0)
{
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1105_;
v___y_1073_ = v___y_1103_;
v___y_1074_ = v___y_1104_;
v_a_1075_ = v___x_1106_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1110_ == 0)
{
if (v___x_1108_ == 0)
{
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1105_;
v___y_1073_ = v___y_1103_;
v___y_1074_ = v___y_1104_;
v_a_1075_ = v___x_1106_;
goto v___jp_1070_;
}
else
{
size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1107_, v___x_1111_, v___x_1112_, v___x_1109_, v___y_1105_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1105_;
v___y_1073_ = v___y_1103_;
v___y_1074_ = v___y_1104_;
v_a_1075_ = v___x_1106_;
goto v___jp_1070_;
}
else
{
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
return v___x_1113_;
}
}
}
else
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1107_, v___x_1114_, v___x_1115_, v___x_1109_, v___y_1105_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_dec_ref_known(v___x_1116_, 1);
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1105_;
v___y_1073_ = v___y_1103_;
v___y_1074_ = v___y_1104_;
v_a_1075_ = v___x_1106_;
goto v___jp_1070_;
}
else
{
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
return v___x_1116_;
}
}
}
}
v___jp_1117_:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_IO_FS_writeFile(v___y_1119_, v___y_1123_);
lean_dec_ref(v___y_1123_);
lean_dec_ref(v___y_1119_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_dec_ref_known(v___x_1124_, 1);
v___y_1102_ = v___y_1118_;
v___y_1103_ = v___y_1120_;
v___y_1104_ = v___y_1121_;
v___y_1105_ = v___y_1122_;
goto v___jp_1101_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_env_904_);
lean_dec_ref(v_dir_900_);
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1129_ = lean_io_error_to_string(v_a_1125_);
v___x_1130_ = 3;
v___x_1131_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*1, v___x_1130_);
lean_inc_ref(v___y_1122_);
v___x_1132_ = lean_apply_2(v___y_1122_, v___x_1131_, lean_box(0));
v___x_1133_ = lean_box(0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1133_);
v___x_1135_ = v___x_1127_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
v___jp_1138_:
{
if (v_a_1144_ == 0)
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = 4;
v___x_1146_ = l_Lake_instDecidableEqInitTemplate(v_tmp_902_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_901_);
v___x_1148_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1147_);
lean_dec_ref(v___x_1147_);
v___y_1118_ = v___y_1139_;
v___y_1119_ = v___y_1140_;
v___y_1120_ = v___y_1141_;
v___y_1121_ = v___y_1142_;
v___y_1122_ = v___y_1143_;
v___y_1123_ = v___x_1148_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_901_);
v___x_1150_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1149_);
lean_dec_ref(v___x_1149_);
v___y_1118_ = v___y_1139_;
v___y_1119_ = v___y_1140_;
v___y_1120_ = v___y_1141_;
v___y_1121_ = v___y_1142_;
v___y_1122_ = v___y_1143_;
v___y_1123_ = v___x_1150_;
goto v___jp_1117_;
}
}
else
{
lean_dec_ref(v___y_1140_);
lean_dec(v_name_901_);
v___y_1102_ = v___y_1139_;
v___y_1103_ = v___y_1141_;
v___y_1104_ = v___y_1142_;
v___y_1105_ = v___y_1143_;
goto v___jp_1101_;
}
}
v___jp_1151_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1156_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v_dir_900_);
v___x_1157_ = l_Lake_joinRelative(v_dir_900_, v___x_1156_);
v___x_1158_ = l_System_FilePath_pathExists(v___x_1157_);
v___x_1159_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1160_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1160_ == 0)
{
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___x_1157_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1155_;
v_a_1144_ = v___x_1158_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1162_ == 0)
{
if (v___x_1160_ == 0)
{
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___x_1157_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1155_;
v_a_1144_ = v___x_1158_;
goto v___jp_1138_;
}
else
{
size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = ((size_t)0ULL);
v___x_1164_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1159_, v___x_1163_, v___x_1164_, v___x_1161_, v___y_1155_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_dec_ref_known(v___x_1165_, 1);
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___x_1157_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1155_;
v_a_1144_ = v___x_1158_;
goto v___jp_1138_;
}
else
{
lean_dec_ref(v___x_1157_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1165_;
}
}
}
else
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1159_, v___x_1166_, v___x_1167_, v___x_1161_, v___y_1155_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_dec_ref_known(v___x_1168_, 1);
v___y_1139_ = v___y_1152_;
v___y_1140_ = v___x_1157_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___y_1155_;
v_a_1144_ = v___x_1158_;
goto v___jp_1138_;
}
else
{
lean_dec_ref(v___x_1157_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1168_;
}
}
}
}
v___jp_1169_:
{
if (v_a_1176_ == 0)
{
uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 1;
v___x_1178_ = l_Lake_instDecidableEqInitTemplate(v_tmp_902_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1175_);
v___x_1180_ = l_IO_FS_writeFile(v___y_1172_, v___x_1179_);
lean_dec_ref(v___x_1179_);
lean_dec_ref(v___y_1172_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_dec_ref_known(v___x_1180_, 1);
v___y_1152_ = v___y_1170_;
v___y_1153_ = v___y_1171_;
v___y_1154_ = v___y_1173_;
v___y_1155_ = v___y_1174_;
goto v___jp_1151_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1193_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1193_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1185_ = lean_io_error_to_string(v_a_1181_);
v___x_1186_ = 3;
v___x_1187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set_uint8(v___x_1187_, sizeof(void*)*1, v___x_1186_);
lean_inc_ref(v___y_1174_);
v___x_1188_ = lean_apply_2(v___y_1174_, v___x_1187_, lean_box(0));
v___x_1189_ = lean_box(0);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1189_);
v___x_1191_ = v___x_1183_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v___y_1175_);
v___x_1194_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1195_ = l_IO_FS_writeFile(v___y_1172_, v___x_1194_);
lean_dec_ref(v___y_1172_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_dec_ref_known(v___x_1195_, 1);
v___y_1152_ = v___y_1170_;
v___y_1153_ = v___y_1171_;
v___y_1154_ = v___y_1173_;
v___y_1155_ = v___y_1174_;
goto v___jp_1151_;
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1200_ = lean_io_error_to_string(v_a_1196_);
v___x_1201_ = 3;
v___x_1202_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*1, v___x_1201_);
lean_inc_ref(v___y_1174_);
v___x_1203_ = lean_apply_2(v___y_1174_, v___x_1202_, lean_box(0));
v___x_1204_ = lean_box(0);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1204_);
v___x_1206_ = v___x_1198_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
else
{
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1172_);
v___y_1152_ = v___y_1170_;
v___y_1153_ = v___y_1171_;
v___y_1154_ = v___y_1173_;
v___y_1155_ = v___y_1174_;
goto v___jp_1151_;
}
}
v___jp_1209_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1215_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_900_);
v___x_1216_ = l_Lake_joinRelative(v_dir_900_, v___x_1215_);
v___x_1217_ = l_System_FilePath_pathExists(v___x_1216_);
v___x_1218_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1219_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1219_ == 0)
{
v___y_1170_ = v___y_1210_;
v___y_1171_ = v___y_1211_;
v___y_1172_ = v___x_1216_;
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1214_;
v_a_1176_ = v___x_1217_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1221_ == 0)
{
if (v___x_1219_ == 0)
{
v___y_1170_ = v___y_1210_;
v___y_1171_ = v___y_1211_;
v___y_1172_ = v___x_1216_;
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1214_;
v_a_1176_ = v___x_1217_;
goto v___jp_1169_;
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1218_, v___x_1222_, v___x_1223_, v___x_1220_, v___y_1212_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_dec_ref_known(v___x_1224_, 1);
v___y_1170_ = v___y_1210_;
v___y_1171_ = v___y_1211_;
v___y_1172_ = v___x_1216_;
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1214_;
v_a_1176_ = v___x_1217_;
goto v___jp_1169_;
}
else
{
lean_dec_ref(v___x_1216_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1224_;
}
}
}
else
{
size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = ((size_t)0ULL);
v___x_1226_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1218_, v___x_1225_, v___x_1226_, v___x_1220_, v___y_1212_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_dec_ref_known(v___x_1227_, 1);
v___y_1170_ = v___y_1210_;
v___y_1171_ = v___y_1211_;
v___y_1172_ = v___x_1216_;
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1214_;
v_a_1176_ = v___x_1217_;
goto v___jp_1169_;
}
else
{
lean_dec_ref(v___x_1216_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1227_;
}
}
}
}
v___jp_1228_:
{
switch(v_tmp_902_)
{
case 0:
{
v___y_1210_ = v___y_1229_;
v___y_1211_ = v___y_1230_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v___y_1232_;
goto v___jp_1209_;
}
case 1:
{
v___y_1210_ = v___y_1229_;
v___y_1211_ = v___y_1230_;
v___y_1212_ = v___y_1233_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v___y_1232_;
goto v___jp_1209_;
}
default: 
{
lean_dec(v___y_1232_);
v___y_1152_ = v___y_1229_;
v___y_1153_ = v___y_1230_;
v___y_1154_ = v___y_1231_;
v___y_1155_ = v___y_1233_;
goto v___jp_1151_;
}
}
}
v___jp_1234_:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_IO_FS_writeFile(v___y_1236_, v___y_1241_);
lean_dec_ref(v___y_1241_);
lean_dec_ref(v___y_1236_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_dec_ref_known(v___x_1242_, 1);
v___y_1229_ = v___y_1235_;
v___y_1230_ = v___y_1237_;
v___y_1231_ = v___y_1239_;
v___y_1232_ = v___y_1240_;
v___y_1233_ = v___y_1238_;
goto v___jp_1228_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1247_ = lean_io_error_to_string(v_a_1243_);
v___x_1248_ = 3;
v___x_1249_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*1, v___x_1248_);
lean_inc_ref(v___y_1238_);
v___x_1250_ = lean_apply_2(v___y_1238_, v___x_1249_, lean_box(0));
v___x_1251_ = lean_box(0);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1251_);
v___x_1253_ = v___x_1245_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
v___jp_1256_:
{
uint8_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = 4;
v___x_1264_ = l_Lake_instDecidableEqInitTemplate(v_tmp_902_, v___x_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = 1;
lean_inc_n(v___y_1261_, 2);
v___x_1266_ = l_Lean_Name_toString(v___y_1261_, v___x_1265_);
v___x_1267_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1266_, v___y_1261_);
lean_dec_ref(v___x_1266_);
v___y_1235_ = v___y_1257_;
v___y_1236_ = v___y_1258_;
v___y_1237_ = v___y_1259_;
v___y_1238_ = v___y_1262_;
v___y_1239_ = v___y_1260_;
v___y_1240_ = v___y_1261_;
v___y_1241_ = v___x_1267_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1268_; 
lean_inc(v___y_1261_);
v___x_1268_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1261_);
v___y_1235_ = v___y_1257_;
v___y_1236_ = v___y_1258_;
v___y_1237_ = v___y_1259_;
v___y_1238_ = v___y_1262_;
v___y_1239_ = v___y_1260_;
v___y_1240_ = v___y_1261_;
v___y_1241_ = v___x_1268_;
goto v___jp_1234_;
}
}
v___jp_1269_:
{
if (v_a_1277_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = l_IO_FS_createDirAll(v___y_1274_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref_known(v___x_1278_, 1);
v___x_1279_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1280_ = l_IO_FS_writeFile(v___y_1270_, v___x_1279_);
lean_dec_ref(v___y_1270_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_dec_ref_known(v___x_1280_, 1);
v___y_1257_ = v___y_1271_;
v___y_1258_ = v___y_1272_;
v___y_1259_ = v___y_1273_;
v___y_1260_ = v___y_1275_;
v___y_1261_ = v___y_1276_;
v___y_1262_ = v_a_906_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1293_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1293_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1285_ = lean_io_error_to_string(v_a_1281_);
v___x_1286_ = 3;
v___x_1287_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*1, v___x_1286_);
lean_inc_ref(v_a_906_);
v___x_1288_ = lean_apply_2(v_a_906_, v___x_1287_, lean_box(0));
v___x_1289_ = lean_box(0);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1289_);
v___x_1291_ = v___x_1283_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v_a_1294_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1296_ = v___x_1278_;
v_isShared_1297_ = v_isSharedCheck_1306_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1278_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1306_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1298_ = lean_io_error_to_string(v_a_1294_);
v___x_1299_ = 3;
v___x_1300_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*1, v___x_1299_);
lean_inc_ref(v_a_906_);
v___x_1301_ = lean_apply_2(v_a_906_, v___x_1300_, lean_box(0));
v___x_1302_ = lean_box(0);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1302_);
v___x_1304_ = v___x_1296_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1270_);
v___y_1257_ = v___y_1271_;
v___y_1258_ = v___y_1272_;
v___y_1259_ = v___y_1273_;
v___y_1260_ = v___y_1275_;
v___y_1261_ = v___y_1276_;
v___y_1262_ = v_a_906_;
goto v___jp_1256_;
}
}
v___jp_1310_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_inc(v___y_1315_);
lean_inc(v___y_1313_);
lean_inc(v_name_901_);
v___x_1316_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_902_, v_lang_903_, v_name_901_, v___y_1313_, v___y_1315_);
v___x_1317_ = l_IO_FS_writeFile(v_configFile_1309_, v___x_1316_);
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_configFile_1309_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_dec_ref_known(v___x_1317_, 1);
if (lean_obj_tag(v___y_1314_) == 1)
{
lean_object* v_val_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_val_1318_ = lean_ctor_get(v___y_1314_, 0);
lean_inc_n(v_val_1318_, 2);
lean_dec_ref_known(v___y_1314_, 1);
v___x_1319_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1320_ = l_System_FilePath_withExtension(v_val_1318_, v___x_1319_);
v___x_1321_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_1320_);
v___x_1322_ = l_Lake_joinRelative(v___x_1320_, v___x_1321_);
v___x_1323_ = l_System_FilePath_pathExists(v___x_1322_);
v___x_1324_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1325_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1325_ == 0)
{
v___y_1270_ = v___x_1322_;
v___y_1271_ = v___y_1311_;
v___y_1272_ = v_val_1318_;
v___y_1273_ = v___y_1312_;
v___y_1274_ = v___x_1320_;
v___y_1275_ = v___y_1315_;
v___y_1276_ = v___y_1313_;
v_a_1277_ = v___x_1323_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1327_ == 0)
{
if (v___x_1325_ == 0)
{
v___y_1270_ = v___x_1322_;
v___y_1271_ = v___y_1311_;
v___y_1272_ = v_val_1318_;
v___y_1273_ = v___y_1312_;
v___y_1274_ = v___x_1320_;
v___y_1275_ = v___y_1315_;
v___y_1276_ = v___y_1313_;
v_a_1277_ = v___x_1323_;
goto v___jp_1269_;
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1324_, v___x_1328_, v___x_1329_, v___x_1326_, v_a_906_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_dec_ref_known(v___x_1330_, 1);
v___y_1270_ = v___x_1322_;
v___y_1271_ = v___y_1311_;
v___y_1272_ = v_val_1318_;
v___y_1273_ = v___y_1312_;
v___y_1274_ = v___x_1320_;
v___y_1275_ = v___y_1315_;
v___y_1276_ = v___y_1313_;
v_a_1277_ = v___x_1323_;
goto v___jp_1269_;
}
else
{
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1320_);
lean_dec(v_val_1318_);
lean_dec(v___y_1315_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1330_;
}
}
}
else
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1324_, v___x_1331_, v___x_1332_, v___x_1326_, v_a_906_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref_known(v___x_1333_, 1);
v___y_1270_ = v___x_1322_;
v___y_1271_ = v___y_1311_;
v___y_1272_ = v_val_1318_;
v___y_1273_ = v___y_1312_;
v___y_1274_ = v___x_1320_;
v___y_1275_ = v___y_1315_;
v___y_1276_ = v___y_1313_;
v_a_1277_ = v___x_1323_;
goto v___jp_1269_;
}
else
{
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1320_);
lean_dec(v_val_1318_);
lean_dec(v___y_1315_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1333_;
}
}
}
}
else
{
lean_dec(v___y_1314_);
v___y_1229_ = v___y_1311_;
v___y_1230_ = v___y_1312_;
v___y_1231_ = v___y_1315_;
v___y_1232_ = v___y_1313_;
v___y_1233_ = v_a_906_;
goto v___jp_1228_;
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v_a_1334_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1336_ = v___x_1317_;
v_isShared_1337_ = v_isSharedCheck_1346_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1317_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1346_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1338_ = lean_io_error_to_string(v_a_1334_);
v___x_1339_ = 3;
v___x_1340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*1, v___x_1339_);
lean_inc_ref(v_a_906_);
v___x_1341_ = lean_apply_2(v_a_906_, v___x_1340_, lean_box(0));
v___x_1342_ = lean_box(0);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1342_);
v___x_1344_ = v___x_1336_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
v___jp_1347_:
{
lean_object* v_lean_1350_; lean_object* v_toolchain_1351_; lean_object* v___x_1352_; 
v_lean_1350_ = lean_ctor_get(v_env_904_, 1);
v_toolchain_1351_ = lean_ctor_get(v_env_904_, 19);
lean_inc_ref(v_toolchain_1351_);
v___x_1352_ = l_Lake_ToolchainVer_ofString(v_toolchain_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_ver_1353_; lean_object* v___x_1354_; 
v_ver_1353_ = lean_ctor_get(v___x_1352_, 1);
lean_inc_ref(v_ver_1353_);
lean_dec_ref_known(v___x_1352_, 2);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_ver_1353_);
lean_inc_ref(v_toolchain_1351_);
lean_inc_ref(v_lean_1350_);
v___y_1311_ = v_lean_1350_;
v___y_1312_ = v_toolchain_1351_;
v___y_1313_ = v_fst_1348_;
v___y_1314_ = v_snd_1349_;
v___y_1315_ = v___x_1354_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1355_; 
lean_dec_ref(v___x_1352_);
v___x_1355_ = lean_box(0);
lean_inc_ref(v_toolchain_1351_);
lean_inc_ref(v_lean_1350_);
v___y_1311_ = v_lean_1350_;
v___y_1312_ = v_toolchain_1351_;
v___y_1313_ = v_fst_1348_;
v___y_1314_ = v_snd_1349_;
v___y_1315_ = v___x_1355_;
goto v___jp_1310_;
}
}
v___jp_1356_:
{
if (v_a_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___y_1357_);
v_fst_1348_ = v___y_1358_;
v_snd_1349_ = v___x_1360_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1361_; 
lean_dec_ref(v___y_1357_);
v___x_1361_ = lean_box(0);
v_fst_1348_ = v___y_1358_;
v_snd_1349_ = v___x_1361_;
goto v___jp_1347_;
}
}
v___jp_1362_:
{
if (v___y_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
lean_inc(v_name_901_);
v___x_1365_ = l_Lake_toUpperCamelCase(v_name_901_);
lean_inc(v___x_1365_);
v___x_1366_ = l_Lean_modToFilePath(v_dir_900_, v___x_1365_, v___y_1363_);
v___x_1367_ = l_System_FilePath_pathExists(v___x_1366_);
v___x_1368_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1369_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1369_ == 0)
{
v___y_1357_ = v___x_1366_;
v___y_1358_ = v___x_1365_;
v_a_1359_ = v___x_1367_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1371_ == 0)
{
if (v___x_1369_ == 0)
{
v___y_1357_ = v___x_1366_;
v___y_1358_ = v___x_1365_;
v_a_1359_ = v___x_1367_;
goto v___jp_1356_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1368_, v___x_1372_, v___x_1373_, v___x_1370_, v_a_906_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_dec_ref_known(v___x_1374_, 1);
v___y_1357_ = v___x_1366_;
v___y_1358_ = v___x_1365_;
v_a_1359_ = v___x_1367_;
goto v___jp_1356_;
}
else
{
lean_dec_ref(v___x_1366_);
lean_dec(v___x_1365_);
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1374_;
}
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1368_, v___x_1375_, v___x_1376_, v___x_1370_, v_a_906_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_dec_ref_known(v___x_1377_, 1);
v___y_1357_ = v___x_1366_;
v___y_1358_ = v___x_1365_;
v_a_1359_ = v___x_1367_;
goto v___jp_1356_;
}
else
{
lean_dec_ref(v___x_1366_);
lean_dec(v___x_1365_);
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1377_;
}
}
}
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_box(0);
lean_inc(v_name_901_);
v_fst_1348_ = v_name_901_;
v_snd_1349_ = v___x_1378_;
goto v___jp_1347_;
}
}
v___jp_1379_:
{
uint8_t v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = 1;
v___x_1383_ = l_Lake_instDecidableEqInitTemplate(v_tmp_902_, v___x_1382_);
if (v___x_1383_ == 0)
{
v___y_1363_ = v___y_1380_;
v___y_1364_ = v_a_1381_;
goto v___jp_1362_;
}
else
{
v___y_1363_ = v___y_1380_;
v___y_1364_ = v___x_1383_;
goto v___jp_1362_;
}
}
v___jp_1384_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1385_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_901_);
v___x_1386_ = l_Lean_modToFilePath(v_dir_900_, v_name_901_, v___x_1385_);
v___x_1387_ = l_System_FilePath_pathExists(v___x_1386_);
lean_dec_ref(v___x_1386_);
v___x_1388_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1389_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1389_ == 0)
{
v___y_1380_ = v___x_1385_;
v_a_1381_ = v___x_1387_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1391_ == 0)
{
if (v___x_1389_ == 0)
{
v___y_1380_ = v___x_1385_;
v_a_1381_ = v___x_1387_;
goto v___jp_1379_;
}
else
{
size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = ((size_t)0ULL);
v___x_1393_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1388_, v___x_1392_, v___x_1393_, v___x_1390_, v_a_906_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_dec_ref_known(v___x_1394_, 1);
v___y_1380_ = v___x_1385_;
v_a_1381_ = v___x_1387_;
goto v___jp_1379_;
}
else
{
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1394_;
}
}
}
else
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1388_, v___x_1395_, v___x_1396_, v___x_1390_, v_a_906_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_dec_ref_known(v___x_1397_, 1);
v___y_1380_ = v___x_1385_;
v_a_1381_ = v___x_1387_;
goto v___jp_1379_;
}
else
{
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___x_1397_;
}
}
}
}
v___jp_1398_:
{
if (lean_obj_tag(v___y_1399_) == 0)
{
lean_dec_ref_known(v___y_1399_, 1);
goto v___jp_1384_;
}
else
{
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
return v___y_1399_;
}
}
v___jp_1401_:
{
if (v___x_1400_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_900_);
v___x_1404_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_900_, v_tmp_902_, v___x_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 2);
v___x_1406_ = lean_array_get_size(v_a_1405_);
v___x_1407_ = lean_nat_dec_lt(v___x_1402_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_dec(v_a_1405_);
goto v___jp_1384_;
}
else
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_nat_dec_le(v___x_1406_, v___x_1406_);
if (v___x_1409_ == 0)
{
if (v___x_1407_ == 0)
{
lean_dec(v_a_1405_);
goto v___jp_1384_;
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1406_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1405_, v___x_1410_, v___x_1411_, v___x_1408_, v_a_906_);
lean_dec(v_a_1405_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_dec_ref_known(v___x_1412_, 1);
goto v___jp_1384_;
}
else
{
v___y_1399_ = v___x_1412_;
goto v___jp_1398_;
}
}
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1406_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1405_, v___x_1413_, v___x_1414_, v___x_1408_, v_a_906_);
lean_dec(v_a_1405_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref_known(v___x_1415_, 1);
goto v___jp_1384_;
}
else
{
v___y_1399_ = v___x_1415_;
goto v___jp_1398_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_a_1416_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1404_, 2);
v___x_1417_ = lean_array_get_size(v_a_1416_);
v___x_1418_ = lean_nat_dec_lt(v___x_1402_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec(v_a_1416_);
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_nat_dec_le(v___x_1417_, v___x_1417_);
if (v___x_1422_ == 0)
{
if (v___x_1418_ == 0)
{
lean_dec(v_a_1416_);
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
goto v___jp_908_;
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1417_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1416_, v___x_1423_, v___x_1424_, v___x_1421_, v_a_906_);
lean_dec(v_a_1416_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_dec_ref_known(v___x_1425_, 1);
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
goto v___jp_908_;
}
else
{
v___y_1399_ = v___x_1425_;
goto v___jp_1398_;
}
}
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1417_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1416_, v___x_1426_, v___x_1427_, v___x_1421_, v_a_906_);
lean_dec(v_a_1416_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_dec_ref_known(v___x_1428_, 1);
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
goto v___jp_908_;
}
else
{
v___y_1399_ = v___x_1428_;
goto v___jp_1398_;
}
}
}
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_configFile_1309_);
lean_dec_ref(v_env_904_);
lean_dec(v_name_901_);
lean_dec_ref(v_dir_900_);
v___x_1429_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
lean_inc_ref(v_a_906_);
v___x_1430_ = lean_apply_2(v_a_906_, v___x_1429_, lean_box(0));
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* v_dir_1443_, lean_object* v_name_1444_, lean_object* v_tmp_1445_, lean_object* v_lang_1446_, lean_object* v_env_1447_, lean_object* v_offline_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
uint8_t v_tmp_boxed_1451_; uint8_t v_lang_boxed_1452_; uint8_t v_offline_boxed_1453_; lean_object* v_res_1454_; 
v_tmp_boxed_1451_ = lean_unbox(v_tmp_1445_);
v_lang_boxed_1452_ = lean_unbox(v_lang_1446_);
v_offline_boxed_1453_ = lean_unbox(v_offline_1448_);
v_res_1454_ = l___private_Lake_CLI_Init_0__Lake_initPkg(v_dir_1443_, v_name_1444_, v_tmp_boxed_1451_, v_lang_boxed_1452_, v_env_1447_, v_offline_boxed_1453_, v_a_1449_);
lean_dec_ref(v_a_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(lean_object* v_s_1455_, lean_object* v_pos_1456_){
_start:
{
lean_object* v_str_1457_; lean_object* v_startInclusive_1458_; lean_object* v_endExclusive_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_str_1457_ = lean_ctor_get(v_s_1455_, 0);
v_startInclusive_1458_ = lean_ctor_get(v_s_1455_, 1);
v_endExclusive_1459_ = lean_ctor_get(v_s_1455_, 2);
v___x_1460_ = lean_nat_add(v_startInclusive_1458_, v_pos_1456_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_nat_sub(v_endExclusive_1459_, v___x_1460_);
v___x_1463_ = lean_nat_dec_eq(v___x_1461_, v___x_1462_);
lean_dec(v___x_1462_);
if (v___x_1463_ == 0)
{
uint32_t v___x_1464_; uint32_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1464_ = lean_string_utf8_get_fast(v_str_1457_, v___x_1460_);
v___x_1465_ = 46;
v___x_1466_ = lean_uint32_dec_eq(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v___x_1460_);
return v_pos_1456_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1467_ = lean_string_utf8_next_fast(v_str_1457_, v___x_1460_);
v___x_1468_ = lean_nat_sub(v___x_1467_, v___x_1460_);
lean_dec(v___x_1460_);
v___x_1469_ = lean_nat_add(v_pos_1456_, v___x_1468_);
lean_dec(v___x_1468_);
v___x_1470_ = lean_nat_dec_lt(v_pos_1456_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v___x_1469_);
return v_pos_1456_;
}
else
{
lean_dec(v_pos_1456_);
v_pos_1456_ = v___x_1469_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1460_);
return v_pos_1456_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* v_s_1472_, lean_object* v_pos_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_1472_, v_pos_1473_);
lean_dec_ref(v_s_1472_);
return v_res_1474_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___f_1476_; 
v___x_1475_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_1476_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1476_, 0, v___x_1475_);
return v___f_1476_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = 92;
v___x_1478_ = lean_box_uint32(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
return v___x_1481_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = 47;
v___x_1483_ = lean_box_uint32(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1);
v___x_1485_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
v___x_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v___x_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(lean_object* v_s_1487_, lean_object* v_a_1488_, uint8_t v_b_1489_){
_start:
{
lean_object* v_str_1490_; lean_object* v_startInclusive_1491_; lean_object* v_endExclusive_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_str_1490_ = lean_ctor_get(v_s_1487_, 0);
v_startInclusive_1491_ = lean_ctor_get(v_s_1487_, 1);
v_endExclusive_1492_ = lean_ctor_get(v_s_1487_, 2);
v___x_1493_ = lean_nat_sub(v_endExclusive_1492_, v_startInclusive_1491_);
v___x_1494_ = lean_nat_dec_eq(v_a_1488_, v___x_1493_);
lean_dec(v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; uint32_t v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1495_ = lean_nat_add(v_startInclusive_1491_, v_a_1488_);
lean_dec(v_a_1488_);
v___x_1496_ = lean_string_utf8_get_fast(v_str_1490_, v___x_1495_);
v___f_1497_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0);
v___x_1498_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2);
v___x_1499_ = lean_box_uint32(v___x_1496_);
v___x_1500_ = l_List_elem___redArg(v___f_1497_, v___x_1499_, v___x_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_string_utf8_next_fast(v_str_1490_, v___x_1495_);
lean_dec(v___x_1495_);
v___x_1502_ = lean_nat_sub(v___x_1501_, v_startInclusive_1491_);
v_a_1488_ = v___x_1502_;
v_b_1489_ = v___x_1500_;
goto _start;
}
else
{
lean_dec(v___x_1495_);
return v___x_1500_;
}
}
else
{
lean_dec(v_a_1488_);
return v_b_1489_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object* v_s_1504_, lean_object* v_a_1505_, lean_object* v_b_1506_){
_start:
{
uint8_t v_b_boxed_1507_; uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_b_boxed_1507_ = lean_unbox(v_b_1506_);
v_res_1508_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1504_, v_a_1505_, v_b_boxed_1507_);
lean_dec_ref(v_s_1504_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object* v_s_1510_){
_start:
{
lean_object* v_searcher_1511_; uint8_t v___x_1512_; uint8_t v___x_1513_; 
v_searcher_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = 0;
v___x_1513_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1510_, v_searcher_1511_, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* v_s_1514_){
_start:
{
uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_res_1515_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v_s_1514_);
lean_dec_ref(v_s_1514_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___f_1519_; 
v___x_1518_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1519_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1519_, 0, v___x_1518_);
return v___f_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* v_pkgName_1539_, lean_object* v_a_1540_){
_start:
{
uint8_t v___y_1553_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1568_ = lean_string_utf8_byte_size(v_pkgName_1539_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_nat_dec_eq(v___x_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
lean_inc_ref(v_pkgName_1539_);
v___x_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1571_, 0, v_pkgName_1539_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
lean_ctor_set(v___x_1571_, 2, v___x_1568_);
v___x_1572_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_1571_, v___x_1569_);
lean_dec_ref_known(v___x_1571_, 3);
v___x_1573_ = lean_nat_dec_eq(v___x_1572_, v___x_1568_);
lean_dec(v___x_1572_);
v___y_1553_ = v___x_1573_;
goto v___jp_1552_;
}
else
{
v___y_1553_ = v___x_1570_;
goto v___jp_1552_;
}
v___jp_1542_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1543_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0));
v___x_1544_ = lean_string_append(v___x_1543_, v_pkgName_1539_);
lean_dec_ref(v_pkgName_1539_);
v___x_1545_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_1546_ = lean_string_append(v___x_1544_, v___x_1545_);
v___x_1547_ = 3;
v___x_1548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*1, v___x_1547_);
v___x_1549_ = lean_array_get_size(v_a_1540_);
v___x_1550_ = lean_array_push(v_a_1540_, v___x_1548_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
return v___x_1551_;
}
v___jp_1552_:
{
if (v___y_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_string_utf8_byte_size(v_pkgName_1539_);
lean_inc_ref(v_pkgName_1539_);
v___x_1556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1556_, 0, v_pkgName_1539_);
lean_ctor_set(v___x_1556_, 1, v___x_1554_);
lean_ctor_set(v___x_1556_, 2, v___x_1555_);
v___x_1557_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_1556_);
lean_dec_ref_known(v___x_1556_, 3);
if (v___x_1557_ == 0)
{
lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___f_1558_ = lean_obj_once(&l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1, &l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once, _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1);
v___x_1559_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_1539_, v___x_1554_);
v___x_1560_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8));
v___x_1561_ = l_List_elem___redArg(v___f_1558_, v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_a_1540_);
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10));
v___x_1565_ = lean_array_get_size(v_a_1540_);
v___x_1566_ = lean_array_push(v_a_1540_, v___x_1564_);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
return v___x_1567_;
}
}
else
{
goto v___jp_1542_;
}
}
else
{
goto v___jp_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* v_pkgName_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_1574_, v_a_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(lean_object* v_s_1578_, lean_object* v_inst_1579_, lean_object* v_R_1580_, lean_object* v_a_1581_, uint8_t v_b_1582_, lean_object* v_c_1583_){
_start:
{
uint8_t v___x_1584_; 
v___x_1584_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_1578_, v_a_1581_, v_b_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object* v_s_1585_, lean_object* v_inst_1586_, lean_object* v_R_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_c_1590_){
_start:
{
uint8_t v_b_boxed_1591_; uint8_t v_res_1592_; lean_object* v_r_1593_; 
v_b_boxed_1591_ = lean_unbox(v_b_1589_);
v_res_1592_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(v_s_1585_, v_inst_1586_, v_R_1587_, v_a_1588_, v_b_boxed_1591_, v_c_1590_);
lean_dec_ref(v_s_1585_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* v_a_1594_, lean_object* v_dir_1595_, lean_object* v_name_1596_, uint8_t v_tmp_1597_, uint8_t v_lang_1598_, lean_object* v_env_1599_, uint8_t v_offline_1600_){
_start:
{
lean_object* v___x_1605_; lean_object* v___y_1607_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1635_; lean_object* v___y_1636_; uint8_t v_a_1637_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; uint8_t v_a_1769_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; uint8_t v_a_1838_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; uint8_t v_a_1870_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v_a_1971_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v_configFile_2003_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___y_2051_; lean_object* v___y_2052_; uint8_t v_a_2053_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2074_; uint8_t v_a_2075_; lean_object* v___y_2093_; uint8_t v___x_2094_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_1605_ = l_Lake_defaultConfigFile;
v___x_2001_ = l_Lake_ConfigLang_fileExtension(v_lang_1598_);
v___x_2002_ = l_System_FilePath_addExtension(v___x_1605_, v___x_2001_);
lean_dec_ref(v___x_2001_);
lean_inc_ref(v_dir_1595_);
v_configFile_2003_ = l_Lake_joinRelative(v_dir_1595_, v___x_2002_);
v___x_2094_ = l_System_FilePath_pathExists(v_configFile_2003_);
v___x_2127_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2128_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2128_ == 0)
{
goto v___jp_2095_;
}
else
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2130_ == 0)
{
if (v___x_2128_ == 0)
{
goto v___jp_2095_;
}
else
{
size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2127_, v___x_2131_, v___x_2132_, v___x_2129_, v_a_1594_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref_known(v___x_2133_, 1);
goto v___jp_2095_;
}
else
{
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2133_;
}
}
}
else
{
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2127_, v___x_2134_, v___x_2135_, v___x_2129_, v_a_1594_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_dec_ref_known(v___x_2136_, 1);
goto v___jp_2095_;
}
else
{
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2136_;
}
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
v___jp_1606_:
{
if (v_offline_1600_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_box(0);
v___x_1611_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
lean_inc_ref(v_dir_1595_);
v___x_1612_ = l_Lake_joinRelative(v_dir_1595_, v___x_1611_);
lean_inc_ref(v___x_1612_);
v___x_1613_ = l_Lake_joinRelative(v___x_1612_, v___x_1605_);
v___x_1614_ = l_Lake_defaultManifestFile;
v___x_1615_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0));
v___x_1616_ = lean_box(1);
v___x_1617_ = l_Lean_Options_empty;
v___x_1618_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_1619_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_1619_, 0, v_env_1599_);
lean_ctor_set(v___x_1619_, 1, v___x_1608_);
lean_ctor_set(v___x_1619_, 2, v_dir_1595_);
lean_ctor_set(v___x_1619_, 3, v___x_1609_);
lean_ctor_set(v___x_1619_, 4, v___x_1610_);
lean_ctor_set(v___x_1619_, 5, v___x_1611_);
lean_ctor_set(v___x_1619_, 6, v___x_1612_);
lean_ctor_set(v___x_1619_, 7, v___x_1605_);
lean_ctor_set(v___x_1619_, 8, v___x_1613_);
lean_ctor_set(v___x_1619_, 9, v___x_1608_);
lean_ctor_set(v___x_1619_, 10, v___x_1614_);
lean_ctor_set(v___x_1619_, 11, v___x_1615_);
lean_ctor_set(v___x_1619_, 12, v___x_1616_);
lean_ctor_set(v___x_1619_, 13, v___x_1617_);
lean_ctor_set(v___x_1619_, 14, v___x_1618_);
lean_ctor_set(v___x_1619_, 15, v___x_1618_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*16, v_offline_1600_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*16 + 1, v_offline_1600_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*16 + 2, v_offline_1600_);
v___x_1620_ = l_Lean_NameSet_empty;
v___x_1621_ = l_Lake_updateManifest(v___x_1619_, v___x_1620_, v___y_1607_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
}
v___jp_1624_:
{
if (lean_obj_tag(v___y_1625_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2));
lean_inc_ref(v___y_1626_);
v___x_1628_ = lean_apply_2(v___y_1626_, v___x_1627_, lean_box(0));
v___y_1607_ = v___y_1626_;
goto v___jp_1606_;
}
else
{
lean_dec_ref_known(v___y_1625_, 1);
v___y_1607_ = v___y_1626_;
goto v___jp_1606_;
}
}
v___jp_1629_:
{
switch(v_tmp_1597_)
{
case 3:
{
v___y_1625_ = v___y_1630_;
v___y_1626_ = v___y_1631_;
goto v___jp_1624_;
}
case 4:
{
v___y_1625_ = v___y_1630_;
v___y_1626_ = v___y_1631_;
goto v___jp_1624_;
}
default: 
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v___y_1630_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
}
}
v___jp_1634_:
{
if (v_a_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4));
lean_inc_ref(v___y_1636_);
v___x_1639_ = lean_apply_2(v___y_1636_, v___x_1638_, lean_box(0));
v___y_1630_ = v___y_1635_;
v___y_1631_ = v___y_1636_;
goto v___jp_1629_;
}
else
{
v___y_1630_ = v___y_1635_;
v___y_1631_ = v___y_1636_;
goto v___jp_1629_;
}
}
v___jp_1640_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; 
v___x_1645_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5));
lean_inc_ref(v_dir_1595_);
v___x_1646_ = l_Lake_joinRelative(v_dir_1595_, v___x_1645_);
v___x_1647_ = 4;
v___x_1648_ = lean_io_prim_handle_mk(v___x_1646_, v___x_1647_);
lean_dec_ref(v___x_1646_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
v___x_1651_ = lean_io_prim_handle_put_str(v_a_1649_, v___x_1650_);
lean_dec(v_a_1649_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
lean_dec_ref_known(v___x_1651_, 1);
v___x_1652_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1595_);
v___x_1653_ = l_Lake_joinRelative(v_dir_1595_, v___x_1652_);
v___x_1654_ = lean_string_utf8_byte_size(v___y_1642_);
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = lean_nat_dec_eq(v___x_1654_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v___y_1641_);
v___x_1657_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2));
v___x_1658_ = lean_string_append(v___y_1642_, v___x_1657_);
v___x_1659_ = l_IO_FS_writeFile(v___x_1653_, v___x_1658_);
lean_dec_ref(v___x_1658_);
lean_dec_ref(v___x_1653_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_dec_ref_known(v___x_1659_, 1);
v___y_1630_ = v___y_1643_;
v___y_1631_ = v___y_1644_;
goto v___jp_1629_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v___y_1643_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1664_ = lean_io_error_to_string(v_a_1660_);
v___x_1665_ = 3;
v___x_1666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*1, v___x_1665_);
lean_inc_ref(v___y_1644_);
v___x_1667_ = lean_apply_2(v___y_1644_, v___x_1666_, lean_box(0));
v___x_1668_ = lean_box(0);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1668_);
v___x_1670_ = v___x_1662_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_githash_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
lean_dec_ref(v___y_1642_);
v_githash_1673_ = lean_ctor_get(v___y_1641_, 1);
lean_inc_ref(v_githash_1673_);
lean_dec_ref(v___y_1641_);
v___x_1674_ = lean_string_utf8_byte_size(v_githash_1673_);
lean_dec_ref(v_githash_1673_);
v___x_1675_ = lean_nat_dec_eq(v___x_1674_, v___x_1655_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = l_System_FilePath_pathExists(v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1677_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1678_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1678_ == 0)
{
v___y_1635_ = v___y_1643_;
v___y_1636_ = v___y_1644_;
v_a_1637_ = v___x_1676_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1680_ == 0)
{
if (v___x_1678_ == 0)
{
v___y_1635_ = v___y_1643_;
v___y_1636_ = v___y_1644_;
v_a_1637_ = v___x_1676_;
goto v___jp_1634_;
}
else
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1677_, v___x_1681_, v___x_1682_, v___x_1679_, v___y_1644_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_dec_ref_known(v___x_1683_, 1);
v___y_1635_ = v___y_1643_;
v___y_1636_ = v___y_1644_;
v_a_1637_ = v___x_1676_;
goto v___jp_1634_;
}
else
{
lean_dec(v___y_1643_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
return v___x_1683_;
}
}
}
else
{
size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = ((size_t)0ULL);
v___x_1685_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1677_, v___x_1684_, v___x_1685_, v___x_1679_, v___y_1644_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_dec_ref_known(v___x_1686_, 1);
v___y_1635_ = v___y_1643_;
v___y_1636_ = v___y_1644_;
v_a_1637_ = v___x_1676_;
goto v___jp_1634_;
}
else
{
lean_dec(v___y_1643_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
return v___x_1686_;
}
}
}
}
else
{
lean_dec_ref(v___x_1653_);
v___y_1630_ = v___y_1643_;
v___y_1631_ = v___y_1644_;
goto v___jp_1629_;
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
v_a_1687_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1689_ = v___x_1651_;
v_isShared_1690_ = v_isSharedCheck_1699_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1651_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1699_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1691_ = lean_io_error_to_string(v_a_1687_);
v___x_1692_ = 3;
v___x_1693_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*1, v___x_1692_);
lean_inc_ref(v___y_1644_);
v___x_1694_ = lean_apply_2(v___y_1644_, v___x_1693_, lean_box(0));
v___x_1695_ = lean_box(0);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1695_);
v___x_1697_ = v___x_1689_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
v_a_1700_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1702_ = v___x_1648_;
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1648_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1712_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1704_ = lean_io_error_to_string(v_a_1700_);
v___x_1705_ = 3;
v___x_1706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*1, v___x_1705_);
lean_inc_ref(v___y_1644_);
v___x_1707_ = lean_apply_2(v___y_1644_, v___x_1706_, lean_box(0));
v___x_1708_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1708_);
v___x_1710_ = v___x_1702_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
v___jp_1713_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12));
lean_inc_ref(v___y_1717_);
v___x_1719_ = lean_apply_2(v___y_1717_, v___x_1718_, lean_box(0));
v___y_1641_ = v___y_1715_;
v___y_1642_ = v___y_1714_;
v___y_1643_ = v___y_1716_;
v___y_1644_ = v___y_1717_;
goto v___jp_1640_;
}
v___jp_1720_:
{
if (lean_obj_tag(v___y_1725_) == 0)
{
lean_dec_ref_known(v___y_1725_, 1);
v___y_1641_ = v___y_1722_;
v___y_1642_ = v___y_1721_;
v___y_1643_ = v___y_1723_;
v___y_1644_ = v___y_1724_;
goto v___jp_1640_;
}
else
{
lean_dec_ref_known(v___y_1725_, 1);
v___y_1714_ = v___y_1721_;
v___y_1715_ = v___y_1722_;
v___y_1716_ = v___y_1723_;
v___y_1717_ = v___y_1724_;
goto v___jp_1713_;
}
}
v___jp_1726_:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = l_Lake_Git_upstreamBranch;
v___x_1732_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1595_);
v___x_1735_ = l_Lake_GitRepo_checkoutBranch(v___x_1731_, v_dir_1595_, v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 2);
v___x_1737_ = lean_array_get_size(v_a_1736_);
v___x_1738_ = lean_nat_dec_lt(v___x_1733_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_dec(v_a_1736_);
v___y_1641_ = v___y_1728_;
v___y_1642_ = v___y_1727_;
v___y_1643_ = v___y_1729_;
v___y_1644_ = v___y_1730_;
goto v___jp_1640_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_nat_dec_le(v___x_1737_, v___x_1737_);
if (v___x_1740_ == 0)
{
if (v___x_1738_ == 0)
{
lean_dec(v_a_1736_);
v___y_1641_ = v___y_1728_;
v___y_1642_ = v___y_1727_;
v___y_1643_ = v___y_1729_;
v___y_1644_ = v___y_1730_;
goto v___jp_1640_;
}
else
{
size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = lean_usize_of_nat(v___x_1737_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1736_, v___x_1741_, v___x_1742_, v___x_1739_, v___y_1730_);
lean_dec(v_a_1736_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_dec_ref_known(v___x_1743_, 1);
v___y_1641_ = v___y_1728_;
v___y_1642_ = v___y_1727_;
v___y_1643_ = v___y_1729_;
v___y_1644_ = v___y_1730_;
goto v___jp_1640_;
}
else
{
v___y_1721_ = v___y_1727_;
v___y_1722_ = v___y_1728_;
v___y_1723_ = v___y_1729_;
v___y_1724_ = v___y_1730_;
v___y_1725_ = v___x_1743_;
goto v___jp_1720_;
}
}
}
else
{
size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = lean_usize_of_nat(v___x_1737_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1736_, v___x_1744_, v___x_1745_, v___x_1739_, v___y_1730_);
lean_dec(v_a_1736_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_dec_ref_known(v___x_1746_, 1);
v___y_1641_ = v___y_1728_;
v___y_1642_ = v___y_1727_;
v___y_1643_ = v___y_1729_;
v___y_1644_ = v___y_1730_;
goto v___jp_1640_;
}
else
{
v___y_1721_ = v___y_1727_;
v___y_1722_ = v___y_1728_;
v___y_1723_ = v___y_1729_;
v___y_1724_ = v___y_1730_;
v___y_1725_ = v___x_1746_;
goto v___jp_1720_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_a_1747_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1735_, 2);
v___x_1748_ = lean_array_get_size(v_a_1747_);
v___x_1749_ = lean_nat_dec_lt(v___x_1733_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec(v_a_1747_);
v___y_1714_ = v___y_1727_;
v___y_1715_ = v___y_1728_;
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_nat_dec_le(v___x_1748_, v___x_1748_);
if (v___x_1751_ == 0)
{
if (v___x_1749_ == 0)
{
lean_dec(v_a_1747_);
v___y_1714_ = v___y_1727_;
v___y_1715_ = v___y_1728_;
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
goto v___jp_1713_;
}
else
{
size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_of_nat(v___x_1748_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1747_, v___x_1752_, v___x_1753_, v___x_1750_, v___y_1730_);
lean_dec(v_a_1747_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_dec_ref_known(v___x_1754_, 1);
v___y_1714_ = v___y_1727_;
v___y_1715_ = v___y_1728_;
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
goto v___jp_1713_;
}
else
{
v___y_1721_ = v___y_1727_;
v___y_1722_ = v___y_1728_;
v___y_1723_ = v___y_1729_;
v___y_1724_ = v___y_1730_;
v___y_1725_ = v___x_1754_;
goto v___jp_1720_;
}
}
}
else
{
size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = lean_usize_of_nat(v___x_1748_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1747_, v___x_1755_, v___x_1756_, v___x_1750_, v___y_1730_);
lean_dec(v_a_1747_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_dec_ref_known(v___x_1757_, 1);
v___y_1714_ = v___y_1727_;
v___y_1715_ = v___y_1728_;
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
goto v___jp_1713_;
}
else
{
v___y_1721_ = v___y_1727_;
v___y_1722_ = v___y_1728_;
v___y_1723_ = v___y_1729_;
v___y_1724_ = v___y_1730_;
v___y_1725_ = v___x_1757_;
goto v___jp_1720_;
}
}
}
}
}
else
{
v___y_1641_ = v___y_1728_;
v___y_1642_ = v___y_1727_;
v___y_1643_ = v___y_1729_;
v___y_1644_ = v___y_1730_;
goto v___jp_1640_;
}
}
v___jp_1758_:
{
if (lean_obj_tag(v___y_1763_) == 0)
{
lean_dec_ref_known(v___y_1763_, 1);
v___y_1727_ = v___y_1760_;
v___y_1728_ = v___y_1759_;
v___y_1729_ = v___y_1761_;
v___y_1730_ = v___y_1762_;
goto v___jp_1726_;
}
else
{
lean_dec_ref_known(v___y_1763_, 1);
v___y_1714_ = v___y_1760_;
v___y_1715_ = v___y_1759_;
v___y_1716_ = v___y_1761_;
v___y_1717_ = v___y_1762_;
goto v___jp_1713_;
}
}
v___jp_1764_:
{
if (v_a_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1595_);
v___x_1772_ = l_Lake_GitRepo_quietInit(v_dir_1595_, v___x_1771_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 1);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 2);
v___x_1774_ = lean_array_get_size(v_a_1773_);
v___x_1775_ = lean_nat_dec_lt(v___x_1770_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_dec(v_a_1773_);
v___y_1727_ = v___y_1766_;
v___y_1728_ = v___y_1765_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1768_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_nat_dec_le(v___x_1774_, v___x_1774_);
if (v___x_1777_ == 0)
{
if (v___x_1775_ == 0)
{
lean_dec(v_a_1773_);
v___y_1727_ = v___y_1766_;
v___y_1728_ = v___y_1765_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1768_;
goto v___jp_1726_;
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_of_nat(v___x_1774_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1773_, v___x_1778_, v___x_1779_, v___x_1776_, v___y_1768_);
lean_dec(v_a_1773_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec_ref_known(v___x_1780_, 1);
v___y_1727_ = v___y_1766_;
v___y_1728_ = v___y_1765_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1768_;
goto v___jp_1726_;
}
else
{
v___y_1759_ = v___y_1765_;
v___y_1760_ = v___y_1766_;
v___y_1761_ = v___y_1767_;
v___y_1762_ = v___y_1768_;
v___y_1763_ = v___x_1780_;
goto v___jp_1758_;
}
}
}
else
{
size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_of_nat(v___x_1774_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1773_, v___x_1781_, v___x_1782_, v___x_1776_, v___y_1768_);
lean_dec(v_a_1773_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec_ref_known(v___x_1783_, 1);
v___y_1727_ = v___y_1766_;
v___y_1728_ = v___y_1765_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___y_1768_;
goto v___jp_1726_;
}
else
{
v___y_1759_ = v___y_1765_;
v___y_1760_ = v___y_1766_;
v___y_1761_ = v___y_1767_;
v___y_1762_ = v___y_1768_;
v___y_1763_ = v___x_1783_;
goto v___jp_1758_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1772_, 1);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1772_, 2);
v___x_1785_ = lean_array_get_size(v_a_1784_);
v___x_1786_ = lean_nat_dec_lt(v___x_1770_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec(v_a_1784_);
v___y_1714_ = v___y_1766_;
v___y_1715_ = v___y_1765_;
v___y_1716_ = v___y_1767_;
v___y_1717_ = v___y_1768_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_nat_dec_le(v___x_1785_, v___x_1785_);
if (v___x_1788_ == 0)
{
if (v___x_1786_ == 0)
{
lean_dec(v_a_1784_);
v___y_1714_ = v___y_1766_;
v___y_1715_ = v___y_1765_;
v___y_1716_ = v___y_1767_;
v___y_1717_ = v___y_1768_;
goto v___jp_1713_;
}
else
{
size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = lean_usize_of_nat(v___x_1785_);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1784_, v___x_1789_, v___x_1790_, v___x_1787_, v___y_1768_);
lean_dec(v_a_1784_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec_ref_known(v___x_1791_, 1);
v___y_1714_ = v___y_1766_;
v___y_1715_ = v___y_1765_;
v___y_1716_ = v___y_1767_;
v___y_1717_ = v___y_1768_;
goto v___jp_1713_;
}
else
{
v___y_1759_ = v___y_1765_;
v___y_1760_ = v___y_1766_;
v___y_1761_ = v___y_1767_;
v___y_1762_ = v___y_1768_;
v___y_1763_ = v___x_1791_;
goto v___jp_1758_;
}
}
}
else
{
size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((size_t)0ULL);
v___x_1793_ = lean_usize_of_nat(v___x_1785_);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_1784_, v___x_1792_, v___x_1793_, v___x_1787_, v___y_1768_);
lean_dec(v_a_1784_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_dec_ref_known(v___x_1794_, 1);
v___y_1714_ = v___y_1766_;
v___y_1715_ = v___y_1765_;
v___y_1716_ = v___y_1767_;
v___y_1717_ = v___y_1768_;
goto v___jp_1713_;
}
else
{
v___y_1759_ = v___y_1765_;
v___y_1760_ = v___y_1766_;
v___y_1761_ = v___y_1767_;
v___y_1762_ = v___y_1768_;
v___y_1763_ = v___x_1794_;
goto v___jp_1758_;
}
}
}
}
}
else
{
v___y_1641_ = v___y_1765_;
v___y_1642_ = v___y_1766_;
v___y_1643_ = v___y_1767_;
v___y_1644_ = v___y_1768_;
goto v___jp_1640_;
}
}
v___jp_1795_:
{
uint8_t v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_inc_ref(v_dir_1595_);
v___x_1800_ = l_Lake_GitRepo_insideWorkTree(v_dir_1595_);
v___x_1801_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1802_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1802_ == 0)
{
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___y_1799_;
v_a_1769_ = v___x_1800_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1804_ == 0)
{
if (v___x_1802_ == 0)
{
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___y_1799_;
v_a_1769_ = v___x_1800_;
goto v___jp_1764_;
}
else
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1801_, v___x_1805_, v___x_1806_, v___x_1803_, v___y_1799_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_dec_ref_known(v___x_1807_, 1);
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___y_1799_;
v_a_1769_ = v___x_1800_;
goto v___jp_1764_;
}
else
{
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
return v___x_1807_;
}
}
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1801_, v___x_1808_, v___x_1809_, v___x_1803_, v___y_1799_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_dec_ref_known(v___x_1810_, 1);
v___y_1765_ = v___y_1796_;
v___y_1766_ = v___y_1797_;
v___y_1767_ = v___y_1798_;
v___y_1768_ = v___y_1799_;
v_a_1769_ = v___x_1800_;
goto v___jp_1764_;
}
else
{
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
return v___x_1810_;
}
}
}
}
v___jp_1811_:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_IO_FS_writeFile(v___y_1815_, v___y_1817_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1815_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_dec_ref_known(v___x_1818_, 1);
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1812_;
v___y_1798_ = v___y_1814_;
v___y_1799_ = v___y_1816_;
goto v___jp_1795_;
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_env_1599_);
lean_dec_ref(v_dir_1595_);
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
lean_inc_ref(v___y_1816_);
v___x_1826_ = lean_apply_2(v___y_1816_, v___x_1825_, lean_box(0));
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
v___jp_1832_:
{
if (v_a_1838_ == 0)
{
uint8_t v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = 4;
v___x_1840_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1597_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1596_);
v___x_1842_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_1841_);
lean_dec_ref(v___x_1841_);
v___y_1812_ = v___y_1834_;
v___y_1813_ = v___y_1833_;
v___y_1814_ = v___y_1835_;
v___y_1815_ = v___y_1836_;
v___y_1816_ = v___y_1837_;
v___y_1817_ = v___x_1842_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_1596_);
v___x_1844_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_1843_);
lean_dec_ref(v___x_1843_);
v___y_1812_ = v___y_1834_;
v___y_1813_ = v___y_1833_;
v___y_1814_ = v___y_1835_;
v___y_1815_ = v___y_1836_;
v___y_1816_ = v___y_1837_;
v___y_1817_ = v___x_1844_;
goto v___jp_1811_;
}
}
else
{
lean_dec_ref(v___y_1836_);
lean_dec(v_name_1596_);
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1834_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___y_1837_;
goto v___jp_1795_;
}
}
v___jp_1845_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1850_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14));
lean_inc_ref(v_dir_1595_);
v___x_1851_ = l_Lake_joinRelative(v_dir_1595_, v___x_1850_);
v___x_1852_ = l_System_FilePath_pathExists(v___x_1851_);
v___x_1853_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1854_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1854_ == 0)
{
v___y_1833_ = v___y_1847_;
v___y_1834_ = v___y_1846_;
v___y_1835_ = v___y_1848_;
v___y_1836_ = v___x_1851_;
v___y_1837_ = v___y_1849_;
v_a_1838_ = v___x_1852_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1856_ == 0)
{
if (v___x_1854_ == 0)
{
v___y_1833_ = v___y_1847_;
v___y_1834_ = v___y_1846_;
v___y_1835_ = v___y_1848_;
v___y_1836_ = v___x_1851_;
v___y_1837_ = v___y_1849_;
v_a_1838_ = v___x_1852_;
goto v___jp_1832_;
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1853_, v___x_1857_, v___x_1858_, v___x_1855_, v___y_1849_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_dec_ref_known(v___x_1859_, 1);
v___y_1833_ = v___y_1847_;
v___y_1834_ = v___y_1846_;
v___y_1835_ = v___y_1848_;
v___y_1836_ = v___x_1851_;
v___y_1837_ = v___y_1849_;
v_a_1838_ = v___x_1852_;
goto v___jp_1832_;
}
else
{
lean_dec_ref(v___x_1851_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_1859_;
}
}
}
else
{
size_t v___x_1860_; size_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = ((size_t)0ULL);
v___x_1861_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1853_, v___x_1860_, v___x_1861_, v___x_1855_, v___y_1849_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec_ref_known(v___x_1862_, 1);
v___y_1833_ = v___y_1847_;
v___y_1834_ = v___y_1846_;
v___y_1835_ = v___y_1848_;
v___y_1836_ = v___x_1851_;
v___y_1837_ = v___y_1849_;
v_a_1838_ = v___x_1852_;
goto v___jp_1832_;
}
else
{
lean_dec_ref(v___x_1851_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_1862_;
}
}
}
}
v___jp_1863_:
{
if (v_a_1870_ == 0)
{
uint8_t v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = 1;
v___x_1872_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1597_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_1868_);
v___x_1874_ = l_IO_FS_writeFile(v___y_1864_, v___x_1873_);
lean_dec_ref(v___x_1873_);
lean_dec_ref(v___y_1864_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref_known(v___x_1874_, 1);
v___y_1846_ = v___y_1866_;
v___y_1847_ = v___y_1865_;
v___y_1848_ = v___y_1867_;
v___y_1849_ = v___y_1869_;
goto v___jp_1845_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
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
lean_inc_ref(v___y_1869_);
v___x_1882_ = lean_apply_2(v___y_1869_, v___x_1881_, lean_box(0));
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
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v___y_1868_);
v___x_1888_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0));
v___x_1889_ = l_IO_FS_writeFile(v___y_1864_, v___x_1888_);
lean_dec_ref(v___y_1864_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_dec_ref_known(v___x_1889_, 1);
v___y_1846_ = v___y_1866_;
v___y_1847_ = v___y_1865_;
v___y_1848_ = v___y_1867_;
v___y_1849_ = v___y_1869_;
goto v___jp_1845_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1894_ = lean_io_error_to_string(v_a_1890_);
v___x_1895_ = 3;
v___x_1896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*1, v___x_1895_);
lean_inc_ref(v___y_1869_);
v___x_1897_ = lean_apply_2(v___y_1869_, v___x_1896_, lean_box(0));
v___x_1898_ = lean_box(0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1898_);
v___x_1900_ = v___x_1892_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
else
{
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1864_);
v___y_1846_ = v___y_1866_;
v___y_1847_ = v___y_1865_;
v___y_1848_ = v___y_1867_;
v___y_1849_ = v___y_1869_;
goto v___jp_1845_;
}
}
v___jp_1903_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1909_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(v_dir_1595_);
v___x_1910_ = l_Lake_joinRelative(v_dir_1595_, v___x_1909_);
v___x_1911_ = l_System_FilePath_pathExists(v___x_1910_);
v___x_1912_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_1913_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_1913_ == 0)
{
v___y_1864_ = v___x_1910_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___y_1904_;
v___y_1867_ = v___y_1906_;
v___y_1868_ = v___y_1907_;
v___y_1869_ = v___y_1908_;
v_a_1870_ = v___x_1911_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_1915_ == 0)
{
if (v___x_1913_ == 0)
{
v___y_1864_ = v___x_1910_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___y_1904_;
v___y_1867_ = v___y_1906_;
v___y_1868_ = v___y_1907_;
v___y_1869_ = v___y_1908_;
v_a_1870_ = v___x_1911_;
goto v___jp_1863_;
}
else
{
size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = ((size_t)0ULL);
v___x_1917_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1912_, v___x_1916_, v___x_1917_, v___x_1914_, v___y_1908_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_dec_ref_known(v___x_1918_, 1);
v___y_1864_ = v___x_1910_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___y_1904_;
v___y_1867_ = v___y_1906_;
v___y_1868_ = v___y_1907_;
v___y_1869_ = v___y_1908_;
v_a_1870_ = v___x_1911_;
goto v___jp_1863_;
}
else
{
lean_dec_ref(v___x_1910_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_1918_;
}
}
}
else
{
size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_1912_, v___x_1919_, v___x_1920_, v___x_1914_, v___y_1908_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_dec_ref_known(v___x_1921_, 1);
v___y_1864_ = v___x_1910_;
v___y_1865_ = v___y_1905_;
v___y_1866_ = v___y_1904_;
v___y_1867_ = v___y_1906_;
v___y_1868_ = v___y_1907_;
v___y_1869_ = v___y_1908_;
v_a_1870_ = v___x_1911_;
goto v___jp_1863_;
}
else
{
lean_dec_ref(v___x_1910_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_1921_;
}
}
}
}
v___jp_1922_:
{
switch(v_tmp_1597_)
{
case 0:
{
v___y_1904_ = v___y_1924_;
v___y_1905_ = v___y_1923_;
v___y_1906_ = v___y_1925_;
v___y_1907_ = v___y_1926_;
v___y_1908_ = v___y_1927_;
goto v___jp_1903_;
}
case 1:
{
v___y_1904_ = v___y_1924_;
v___y_1905_ = v___y_1923_;
v___y_1906_ = v___y_1925_;
v___y_1907_ = v___y_1926_;
v___y_1908_ = v___y_1927_;
goto v___jp_1903_;
}
default: 
{
lean_dec(v___y_1926_);
v___y_1846_ = v___y_1924_;
v___y_1847_ = v___y_1923_;
v___y_1848_ = v___y_1925_;
v___y_1849_ = v___y_1927_;
goto v___jp_1845_;
}
}
}
v___jp_1928_:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_IO_FS_writeFile(v___y_1932_, v___y_1935_);
lean_dec_ref(v___y_1935_);
lean_dec_ref(v___y_1932_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1929_;
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1933_;
v___y_1927_ = v___y_1934_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v___y_1933_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1949_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1949_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1941_ = lean_io_error_to_string(v_a_1937_);
v___x_1942_ = 3;
v___x_1943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*1, v___x_1942_);
lean_inc_ref(v___y_1934_);
v___x_1944_ = lean_apply_2(v___y_1934_, v___x_1943_, lean_box(0));
v___x_1945_ = lean_box(0);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1945_);
v___x_1947_ = v___x_1939_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
v___jp_1950_:
{
uint8_t v___x_1957_; uint8_t v___x_1958_; 
v___x_1957_ = 4;
v___x_1958_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1597_, v___x_1957_);
if (v___x_1958_ == 0)
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = 1;
lean_inc_n(v___y_1955_, 2);
v___x_1960_ = l_Lean_Name_toString(v___y_1955_, v___x_1959_);
v___x_1961_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v___x_1960_, v___y_1955_);
lean_dec_ref(v___x_1960_);
v___y_1929_ = v___y_1952_;
v___y_1930_ = v___y_1951_;
v___y_1931_ = v___y_1953_;
v___y_1932_ = v___y_1954_;
v___y_1933_ = v___y_1955_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___x_1961_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1962_; 
lean_inc(v___y_1955_);
v___x_1962_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_1955_);
v___y_1929_ = v___y_1952_;
v___y_1930_ = v___y_1951_;
v___y_1931_ = v___y_1953_;
v___y_1932_ = v___y_1954_;
v___y_1933_ = v___y_1955_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___x_1962_;
goto v___jp_1928_;
}
}
v___jp_1963_:
{
if (v_a_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = l_IO_FS_createDirAll(v___y_1967_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1972_, 1);
v___x_1973_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0));
v___x_1974_ = l_IO_FS_writeFile(v___y_1970_, v___x_1973_);
lean_dec_ref(v___y_1970_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_dec_ref_known(v___x_1974_, 1);
v___y_1951_ = v___y_1965_;
v___y_1952_ = v___y_1964_;
v___y_1953_ = v___y_1966_;
v___y_1954_ = v___y_1968_;
v___y_1955_ = v___y_1969_;
v___y_1956_ = v_a_1594_;
goto v___jp_1950_;
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1987_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1987_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1979_ = lean_io_error_to_string(v_a_1975_);
v___x_1980_ = 3;
v___x_1981_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*1, v___x_1980_);
lean_inc_ref(v_a_1594_);
v___x_1982_ = lean_apply_2(v_a_1594_, v___x_1981_, lean_box(0));
v___x_1983_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1983_);
v___x_1985_ = v___x_1977_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v_a_1988_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1990_ = v___x_1972_;
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1972_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1992_ = lean_io_error_to_string(v_a_1988_);
v___x_1993_ = 3;
v___x_1994_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*1, v___x_1993_);
lean_inc_ref(v_a_1594_);
v___x_1995_ = lean_apply_2(v_a_1594_, v___x_1994_, lean_box(0));
v___x_1996_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1996_);
v___x_1998_ = v___x_1990_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_dec_ref(v___y_1970_);
lean_dec_ref(v___y_1967_);
v___y_1951_ = v___y_1965_;
v___y_1952_ = v___y_1964_;
v___y_1953_ = v___y_1966_;
v___y_1954_ = v___y_1968_;
v___y_1955_ = v___y_1969_;
v___y_1956_ = v_a_1594_;
goto v___jp_1950_;
}
}
v___jp_2004_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_inc(v___y_2009_);
lean_inc(v___y_2007_);
lean_inc(v_name_1596_);
v___x_2010_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(v_tmp_1597_, v_lang_1598_, v_name_1596_, v___y_2007_, v___y_2009_);
v___x_2011_ = l_IO_FS_writeFile(v_configFile_2003_, v___x_2010_);
lean_dec_ref(v___x_2010_);
lean_dec_ref(v_configFile_2003_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
if (lean_obj_tag(v___y_2008_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_val_2012_ = lean_ctor_get(v___y_2008_, 0);
lean_inc_n(v_val_2012_, 2);
lean_dec_ref_known(v___y_2008_, 1);
v___x_2013_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0));
v___x_2014_ = l_System_FilePath_withExtension(v_val_2012_, v___x_2013_);
v___x_2015_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15));
lean_inc_ref(v___x_2014_);
v___x_2016_ = l_Lake_joinRelative(v___x_2014_, v___x_2015_);
v___x_2017_ = l_System_FilePath_pathExists(v___x_2016_);
v___x_2018_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2019_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2019_ == 0)
{
v___y_1964_ = v___y_2005_;
v___y_1965_ = v___y_2006_;
v___y_1966_ = v___y_2009_;
v___y_1967_ = v___x_2014_;
v___y_1968_ = v_val_2012_;
v___y_1969_ = v___y_2007_;
v___y_1970_ = v___x_2016_;
v_a_1971_ = v___x_2017_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2021_ == 0)
{
if (v___x_2019_ == 0)
{
v___y_1964_ = v___y_2005_;
v___y_1965_ = v___y_2006_;
v___y_1966_ = v___y_2009_;
v___y_1967_ = v___x_2014_;
v___y_1968_ = v_val_2012_;
v___y_1969_ = v___y_2007_;
v___y_1970_ = v___x_2016_;
v_a_1971_ = v___x_2017_;
goto v___jp_1963_;
}
else
{
size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2018_, v___x_2022_, v___x_2023_, v___x_2020_, v_a_1594_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_dec_ref_known(v___x_2024_, 1);
v___y_1964_ = v___y_2005_;
v___y_1965_ = v___y_2006_;
v___y_1966_ = v___y_2009_;
v___y_1967_ = v___x_2014_;
v___y_1968_ = v_val_2012_;
v___y_1969_ = v___y_2007_;
v___y_1970_ = v___x_2016_;
v_a_1971_ = v___x_2017_;
goto v___jp_1963_;
}
else
{
lean_dec_ref(v___x_2016_);
lean_dec_ref(v___x_2014_);
lean_dec(v_val_2012_);
lean_dec(v___y_2009_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2024_;
}
}
}
else
{
size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = ((size_t)0ULL);
v___x_2026_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2018_, v___x_2025_, v___x_2026_, v___x_2020_, v_a_1594_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec_ref_known(v___x_2027_, 1);
v___y_1964_ = v___y_2005_;
v___y_1965_ = v___y_2006_;
v___y_1966_ = v___y_2009_;
v___y_1967_ = v___x_2014_;
v___y_1968_ = v_val_2012_;
v___y_1969_ = v___y_2007_;
v___y_1970_ = v___x_2016_;
v_a_1971_ = v___x_2017_;
goto v___jp_1963_;
}
else
{
lean_dec_ref(v___x_2016_);
lean_dec_ref(v___x_2014_);
lean_dec(v_val_2012_);
lean_dec(v___y_2009_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2027_;
}
}
}
}
else
{
lean_dec(v___y_2008_);
v___y_1923_ = v___y_2006_;
v___y_1924_ = v___y_2005_;
v___y_1925_ = v___y_2009_;
v___y_1926_ = v___y_2007_;
v___y_1927_ = v_a_1594_;
goto v___jp_1922_;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v_a_2028_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2030_ = v___x_2011_;
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2011_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2032_ = lean_io_error_to_string(v_a_2028_);
v___x_2033_ = 3;
v___x_2034_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*1, v___x_2033_);
lean_inc_ref(v_a_1594_);
v___x_2035_ = lean_apply_2(v_a_1594_, v___x_2034_, lean_box(0));
v___x_2036_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2036_);
v___x_2038_ = v___x_2030_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
v___jp_2041_:
{
lean_object* v_lean_2044_; lean_object* v_toolchain_2045_; lean_object* v___x_2046_; 
v_lean_2044_ = lean_ctor_get(v_env_1599_, 1);
v_toolchain_2045_ = lean_ctor_get(v_env_1599_, 19);
lean_inc_ref(v_toolchain_2045_);
v___x_2046_ = l_Lake_ToolchainVer_ofString(v_toolchain_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_ver_2047_; lean_object* v___x_2048_; 
v_ver_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc_ref(v_ver_2047_);
lean_dec_ref_known(v___x_2046_, 2);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_ver_2047_);
lean_inc_ref(v_lean_2044_);
lean_inc_ref(v_toolchain_2045_);
v___y_2005_ = v_toolchain_2045_;
v___y_2006_ = v_lean_2044_;
v___y_2007_ = v_fst_2042_;
v___y_2008_ = v_snd_2043_;
v___y_2009_ = v___x_2048_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2049_; 
lean_dec_ref(v___x_2046_);
v___x_2049_ = lean_box(0);
lean_inc_ref(v_lean_2044_);
lean_inc_ref(v_toolchain_2045_);
v___y_2005_ = v_toolchain_2045_;
v___y_2006_ = v_lean_2044_;
v___y_2007_ = v_fst_2042_;
v___y_2008_ = v_snd_2043_;
v___y_2009_ = v___x_2049_;
goto v___jp_2004_;
}
}
v___jp_2050_:
{
if (v_a_2053_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___y_2051_);
v_fst_2042_ = v___y_2052_;
v_snd_2043_ = v___x_2054_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2055_; 
lean_dec_ref(v___y_2051_);
v___x_2055_ = lean_box(0);
v_fst_2042_ = v___y_2052_;
v_snd_2043_ = v___x_2055_;
goto v___jp_2041_;
}
}
v___jp_2056_:
{
if (v___y_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
lean_inc(v_name_1596_);
v___x_2059_ = l_Lake_toUpperCamelCase(v_name_1596_);
lean_inc(v___x_2059_);
v___x_2060_ = l_Lean_modToFilePath(v_dir_1595_, v___x_2059_, v___y_2057_);
v___x_2061_ = l_System_FilePath_pathExists(v___x_2060_);
v___x_2062_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2063_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2063_ == 0)
{
v___y_2051_ = v___x_2060_;
v___y_2052_ = v___x_2059_;
v_a_2053_ = v___x_2061_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2065_ == 0)
{
if (v___x_2063_ == 0)
{
v___y_2051_ = v___x_2060_;
v___y_2052_ = v___x_2059_;
v_a_2053_ = v___x_2061_;
goto v___jp_2050_;
}
else
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2062_, v___x_2066_, v___x_2067_, v___x_2064_, v_a_1594_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_dec_ref_known(v___x_2068_, 1);
v___y_2051_ = v___x_2060_;
v___y_2052_ = v___x_2059_;
v_a_2053_ = v___x_2061_;
goto v___jp_2050_;
}
else
{
lean_dec_ref(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2068_;
}
}
}
else
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2062_, v___x_2069_, v___x_2070_, v___x_2064_, v_a_1594_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_dec_ref_known(v___x_2071_, 1);
v___y_2051_ = v___x_2060_;
v___y_2052_ = v___x_2059_;
v_a_2053_ = v___x_2061_;
goto v___jp_2050_;
}
else
{
lean_dec_ref(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_box(0);
lean_inc(v_name_1596_);
v_fst_2042_ = v_name_1596_;
v_snd_2043_ = v___x_2072_;
goto v___jp_2041_;
}
}
v___jp_2073_:
{
uint8_t v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = 1;
v___x_2077_ = l_Lake_instDecidableEqInitTemplate(v_tmp_1597_, v___x_2076_);
if (v___x_2077_ == 0)
{
v___y_2057_ = v___y_2074_;
v___y_2058_ = v_a_2075_;
goto v___jp_2056_;
}
else
{
v___y_2057_ = v___y_2074_;
v___y_2058_ = v___x_2077_;
goto v___jp_2056_;
}
}
v___jp_2078_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2079_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16));
lean_inc(v_name_1596_);
v___x_2080_ = l_Lean_modToFilePath(v_dir_1595_, v_name_1596_, v___x_2079_);
v___x_2081_ = l_System_FilePath_pathExists(v___x_2080_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
v___x_2083_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
if (v___x_2083_ == 0)
{
v___y_2074_ = v___x_2079_;
v_a_2075_ = v___x_2081_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_uint8_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
if (v___x_2085_ == 0)
{
if (v___x_2083_ == 0)
{
v___y_2074_ = v___x_2079_;
v_a_2075_ = v___x_2081_;
goto v___jp_2073_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2082_, v___x_2086_, v___x_2087_, v___x_2084_, v_a_1594_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_dec_ref_known(v___x_2088_, 1);
v___y_2074_ = v___x_2079_;
v_a_2075_ = v___x_2081_;
goto v___jp_2073_;
}
else
{
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2088_;
}
}
}
else
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = lean_usize_once(&l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10, &l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once, _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_2082_, v___x_2089_, v___x_2090_, v___x_2084_, v_a_1594_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_dec_ref_known(v___x_2091_, 1);
v___y_2074_ = v___x_2079_;
v_a_2075_ = v___x_2081_;
goto v___jp_2073_;
}
else
{
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___x_2091_;
}
}
}
}
v___jp_2092_:
{
if (lean_obj_tag(v___y_2093_) == 0)
{
lean_dec_ref_known(v___y_2093_, 1);
goto v___jp_2078_;
}
else
{
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
return v___y_2093_;
}
}
v___jp_2095_:
{
if (v___x_2094_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_dir_1595_);
v___x_2098_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(v_dir_1595_, v_tmp_1597_, v___x_2097_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 2);
v___x_2100_ = lean_array_get_size(v_a_2099_);
v___x_2101_ = lean_nat_dec_lt(v___x_2096_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec(v_a_2099_);
goto v___jp_2078_;
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_nat_dec_le(v___x_2100_, v___x_2100_);
if (v___x_2103_ == 0)
{
if (v___x_2101_ == 0)
{
lean_dec(v_a_2099_);
goto v___jp_2078_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = lean_usize_of_nat(v___x_2100_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2099_, v___x_2104_, v___x_2105_, v___x_2102_, v_a_1594_);
lean_dec(v_a_2099_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_dec_ref_known(v___x_2106_, 1);
goto v___jp_2078_;
}
else
{
v___y_2093_ = v___x_2106_;
goto v___jp_2092_;
}
}
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2100_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2099_, v___x_2107_, v___x_2108_, v___x_2102_, v_a_1594_);
lean_dec(v_a_2099_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_dec_ref_known(v___x_2109_, 1);
goto v___jp_2078_;
}
else
{
v___y_2093_ = v___x_2109_;
goto v___jp_2092_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_a_2110_ = lean_ctor_get(v___x_2098_, 1);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2098_, 2);
v___x_2111_ = lean_array_get_size(v_a_2110_);
v___x_2112_ = lean_nat_dec_lt(v___x_2096_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec(v_a_2110_);
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_nat_dec_le(v___x_2111_, v___x_2111_);
if (v___x_2116_ == 0)
{
if (v___x_2112_ == 0)
{
lean_dec(v_a_2110_);
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
goto v___jp_1602_;
}
else
{
size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = lean_usize_of_nat(v___x_2111_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2110_, v___x_2117_, v___x_2118_, v___x_2115_, v_a_1594_);
lean_dec(v_a_2110_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_dec_ref_known(v___x_2119_, 1);
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
goto v___jp_1602_;
}
else
{
v___y_2093_ = v___x_2119_;
goto v___jp_2092_;
}
}
}
else
{
size_t v___x_2120_; size_t v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = lean_usize_of_nat(v___x_2111_);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2110_, v___x_2120_, v___x_2121_, v___x_2115_, v_a_1594_);
lean_dec(v_a_2110_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_dec_ref_known(v___x_2122_, 1);
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
goto v___jp_1602_;
}
else
{
v___y_2093_ = v___x_2122_;
goto v___jp_2092_;
}
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v_configFile_2003_);
lean_dec_ref(v_env_1599_);
lean_dec(v_name_1596_);
lean_dec_ref(v_dir_1595_);
v___x_2123_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18));
lean_inc_ref(v_a_1594_);
v___x_2124_ = lean_apply_2(v_a_1594_, v___x_2123_, lean_box(0));
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* v_a_2137_, lean_object* v_dir_2138_, lean_object* v_name_2139_, lean_object* v_tmp_2140_, lean_object* v_lang_2141_, lean_object* v_env_2142_, lean_object* v_offline_2143_, lean_object* v_a_2144_){
_start:
{
uint8_t v_tmp_boxed_2145_; uint8_t v_lang_boxed_2146_; uint8_t v_offline_boxed_2147_; lean_object* v_res_2148_; 
v_tmp_boxed_2145_ = lean_unbox(v_tmp_2140_);
v_lang_boxed_2146_ = lean_unbox(v_lang_2141_);
v_offline_boxed_2147_ = lean_unbox(v_offline_2143_);
v_res_2148_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2137_, v_dir_2138_, v_name_2139_, v_tmp_boxed_2145_, v_lang_boxed_2146_, v_env_2142_, v_offline_boxed_2147_);
lean_dec_ref(v_a_2137_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* v_name_2150_, uint8_t v_tmp_2151_, uint8_t v_lang_2152_, lean_object* v_env_2153_, lean_object* v_cwd_2154_, uint8_t v_offline_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___y_2162_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v_a_2183_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4));
v___x_2219_ = lean_string_dec_eq(v_name_2150_, v___x_2218_);
if (v___x_2219_ == 0)
{
v_a_2183_ = v_name_2150_;
goto v___jp_2182_;
}
else
{
lean_object* v___x_2220_; 
lean_dec_ref(v_name_2150_);
lean_inc_ref(v_cwd_2154_);
v___x_2220_ = lean_io_realpath(v_cwd_2154_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2238_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2238_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2238_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; 
lean_inc(v_a_2221_);
v___x_2225_ = l_System_FilePath_fileName(v_a_2221_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
v___x_2226_ = ((lean_object*)(l_Lake_init___closed__0));
v___x_2227_ = lean_string_append(v___x_2226_, v_a_2221_);
lean_dec(v_a_2221_);
v___x_2228_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6));
v___x_2229_ = lean_string_append(v___x_2227_, v___x_2228_);
v___x_2230_ = 3;
v___x_2231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*1, v___x_2230_);
lean_inc_ref(v_a_2156_);
v___x_2232_ = lean_apply_2(v_a_2156_, v___x_2231_, lean_box(0));
v___x_2233_ = lean_box(0);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2233_);
v___x_2235_ = v___x_2223_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
lean_object* v_val_2237_; 
lean_del_object(v___x_2223_);
lean_dec(v_a_2221_);
v_val_2237_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2225_, 1);
v_a_2183_ = v_val_2237_;
goto v___jp_2182_;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
v_a_2239_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2241_ = v___x_2220_;
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2220_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2243_ = lean_io_error_to_string(v_a_2239_);
v___x_2244_ = 3;
v___x_2245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*1, v___x_2244_);
lean_inc_ref(v_a_2156_);
v___x_2246_ = lean_apply_2(v_a_2156_, v___x_2245_, lean_box(0));
v___x_2247_ = lean_box(0);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2247_);
v___x_2249_ = v___x_2241_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
v___jp_2158_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; 
lean_inc_ref(v_cwd_2154_);
v___x_2163_ = l_IO_FS_createDirAll(v_cwd_2154_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v___x_2163_, 1);
v___x_2164_ = l_Lake_stringToLegalOrSimpleName(v___y_2162_);
v___x_2165_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2156_, v_cwd_2154_, v___x_2164_, v_tmp_2151_, v_lang_2152_, v_env_2153_, v_offline_2155_);
return v___x_2165_;
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___y_2162_);
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
v_a_2166_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2168_ = v___x_2163_;
v_isShared_2169_ = v_isSharedCheck_2178_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2163_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2178_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2170_ = lean_io_error_to_string(v_a_2166_);
v___x_2171_ = 3;
v___x_2172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*1, v___x_2171_);
lean_inc_ref(v_a_2156_);
v___x_2173_ = lean_apply_2(v_a_2156_, v___x_2172_, lean_box(0));
v___x_2174_ = lean_box(0);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2174_);
v___x_2176_ = v___x_2168_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
v___jp_2179_:
{
if (lean_obj_tag(v___y_2181_) == 0)
{
lean_dec_ref_known(v___y_2181_, 1);
v___y_2162_ = v___y_2180_;
goto v___jp_2161_;
}
else
{
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
return v___y_2181_;
}
}
v___jp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_str_2188_; lean_object* v_startInclusive_2189_; lean_object* v_endExclusive_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_string_utf8_byte_size(v_a_2183_);
v___x_2186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2183_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
v___x_2187_ = l_String_Slice_trimAscii(v___x_2186_);
v_str_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc_ref(v_str_2188_);
v_startInclusive_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_startInclusive_2189_);
v_endExclusive_2190_ = lean_ctor_get(v___x_2187_, 2);
lean_inc(v_endExclusive_2190_);
lean_dec_ref(v___x_2187_);
v___x_2191_ = lean_string_utf8_extract_fast(v_str_2188_, v_startInclusive_2189_, v_endExclusive_2190_);
lean_dec(v_endExclusive_2190_);
lean_dec(v_startInclusive_2189_);
lean_dec_ref(v_str_2188_);
v___x_2192_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v___x_2191_);
v___x_2193_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_2191_, v___x_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 2);
v___x_2195_ = lean_array_get_size(v_a_2194_);
v___x_2196_ = lean_nat_dec_lt(v___x_2184_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_dec(v_a_2194_);
v___y_2162_ = v___x_2191_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_box(0);
v___x_2198_ = lean_nat_dec_le(v___x_2195_, v___x_2195_);
if (v___x_2198_ == 0)
{
if (v___x_2196_ == 0)
{
lean_dec(v_a_2194_);
v___y_2162_ = v___x_2191_;
goto v___jp_2161_;
}
else
{
size_t v___x_2199_; size_t v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((size_t)0ULL);
v___x_2200_ = lean_usize_of_nat(v___x_2195_);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2194_, v___x_2199_, v___x_2200_, v___x_2197_, v_a_2156_);
lean_dec(v_a_2194_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_dec_ref_known(v___x_2201_, 1);
v___y_2162_ = v___x_2191_;
goto v___jp_2161_;
}
else
{
v___y_2180_ = v___x_2191_;
v___y_2181_ = v___x_2201_;
goto v___jp_2179_;
}
}
}
else
{
size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = lean_usize_of_nat(v___x_2195_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2194_, v___x_2202_, v___x_2203_, v___x_2197_, v_a_2156_);
lean_dec(v_a_2194_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_dec_ref_known(v___x_2204_, 1);
v___y_2162_ = v___x_2191_;
goto v___jp_2161_;
}
else
{
v___y_2180_ = v___x_2191_;
v___y_2181_ = v___x_2204_;
goto v___jp_2179_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v_a_2205_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2193_, 2);
v___x_2206_ = lean_array_get_size(v_a_2205_);
v___x_2207_ = lean_nat_dec_lt(v___x_2184_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_a_2205_);
lean_dec_ref(v___x_2191_);
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_nat_dec_le(v___x_2206_, v___x_2206_);
if (v___x_2211_ == 0)
{
if (v___x_2207_ == 0)
{
lean_dec(v_a_2205_);
lean_dec_ref(v___x_2191_);
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
goto v___jp_2158_;
}
else
{
size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = lean_usize_of_nat(v___x_2206_);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2205_, v___x_2212_, v___x_2213_, v___x_2210_, v_a_2156_);
lean_dec(v_a_2205_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_dec_ref_known(v___x_2214_, 1);
lean_dec_ref(v___x_2191_);
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
goto v___jp_2158_;
}
else
{
v___y_2180_ = v___x_2191_;
v___y_2181_ = v___x_2214_;
goto v___jp_2179_;
}
}
}
else
{
size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = lean_usize_of_nat(v___x_2206_);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2205_, v___x_2215_, v___x_2216_, v___x_2210_, v_a_2156_);
lean_dec(v_a_2205_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
lean_dec_ref(v___x_2191_);
lean_dec_ref(v_cwd_2154_);
lean_dec_ref(v_env_2153_);
goto v___jp_2158_;
}
else
{
v___y_2180_ = v___x_2191_;
v___y_2181_ = v___x_2217_;
goto v___jp_2179_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* v_name_2252_, lean_object* v_tmp_2253_, lean_object* v_lang_2254_, lean_object* v_env_2255_, lean_object* v_cwd_2256_, lean_object* v_offline_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
uint8_t v_tmp_boxed_2260_; uint8_t v_lang_boxed_2261_; uint8_t v_offline_boxed_2262_; lean_object* v_res_2263_; 
v_tmp_boxed_2260_ = lean_unbox(v_tmp_2253_);
v_lang_boxed_2261_ = lean_unbox(v_lang_2254_);
v_offline_boxed_2262_ = lean_unbox(v_offline_2257_);
v_res_2263_ = l_Lake_init(v_name_2252_, v_tmp_boxed_2260_, v_lang_boxed_2261_, v_env_2255_, v_cwd_2256_, v_offline_boxed_2262_, v_a_2258_);
lean_dec_ref(v_a_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* v_name_2264_, uint8_t v_tmp_2265_, uint8_t v_lang_2266_, lean_object* v_env_2267_, lean_object* v_cwd_2268_, uint8_t v_offline_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_str_2279_; lean_object* v_startInclusive_2280_; lean_object* v_endExclusive_2281_; lean_object* v_name_2282_; lean_object* v___y_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_string_utf8_byte_size(v_name_2264_);
v___x_2277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2277_, 0, v_name_2264_);
lean_ctor_set(v___x_2277_, 1, v___x_2275_);
lean_ctor_set(v___x_2277_, 2, v___x_2276_);
v___x_2278_ = l_String_Slice_trimAscii(v___x_2277_);
v_str_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref(v_str_2279_);
v_startInclusive_2280_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_startInclusive_2280_);
v_endExclusive_2281_ = lean_ctor_get(v___x_2278_, 2);
lean_inc(v_endExclusive_2281_);
lean_dec_ref(v___x_2278_);
v_name_2282_ = lean_string_utf8_extract_fast(v_str_2279_, v_startInclusive_2280_, v_endExclusive_2281_);
lean_dec(v_endExclusive_2281_);
lean_dec(v_startInclusive_2280_);
lean_dec_ref(v_str_2279_);
v___x_2304_ = ((lean_object*)(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6));
lean_inc_ref(v_name_2282_);
v___x_2305_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_2282_, v___x_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 2);
v___x_2307_ = lean_array_get_size(v_a_2306_);
v___x_2308_ = lean_nat_dec_lt(v___x_2275_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_a_2306_);
goto v___jp_2283_;
}
else
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_nat_dec_le(v___x_2307_, v___x_2307_);
if (v___x_2310_ == 0)
{
if (v___x_2308_ == 0)
{
lean_dec(v_a_2306_);
goto v___jp_2283_;
}
else
{
size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = lean_usize_of_nat(v___x_2307_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2306_, v___x_2311_, v___x_2312_, v___x_2309_, v_a_2270_);
lean_dec(v_a_2306_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref_known(v___x_2313_, 1);
goto v___jp_2283_;
}
else
{
v___y_2303_ = v___x_2313_;
goto v___jp_2302_;
}
}
}
else
{
size_t v___x_2314_; size_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = ((size_t)0ULL);
v___x_2315_ = lean_usize_of_nat(v___x_2307_);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2306_, v___x_2314_, v___x_2315_, v___x_2309_, v_a_2270_);
lean_dec(v_a_2306_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_dec_ref_known(v___x_2316_, 1);
goto v___jp_2283_;
}
else
{
v___y_2303_ = v___x_2316_;
goto v___jp_2302_;
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v_a_2317_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2305_, 2);
v___x_2318_ = lean_array_get_size(v_a_2317_);
v___x_2319_ = lean_nat_dec_lt(v___x_2275_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_a_2317_);
lean_dec_ref(v_name_2282_);
lean_dec_ref(v_cwd_2268_);
lean_dec_ref(v_env_2267_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_nat_dec_le(v___x_2318_, v___x_2318_);
if (v___x_2323_ == 0)
{
if (v___x_2319_ == 0)
{
lean_dec(v_a_2317_);
lean_dec_ref(v_name_2282_);
lean_dec_ref(v_cwd_2268_);
lean_dec_ref(v_env_2267_);
goto v___jp_2272_;
}
else
{
size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = lean_usize_of_nat(v___x_2318_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2317_, v___x_2324_, v___x_2325_, v___x_2322_, v_a_2270_);
lean_dec(v_a_2317_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_dec_ref_known(v___x_2326_, 1);
lean_dec_ref(v_name_2282_);
lean_dec_ref(v_cwd_2268_);
lean_dec_ref(v_env_2267_);
goto v___jp_2272_;
}
else
{
v___y_2303_ = v___x_2326_;
goto v___jp_2302_;
}
}
}
else
{
size_t v___x_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = lean_usize_of_nat(v___x_2318_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_2317_, v___x_2327_, v___x_2328_, v___x_2322_, v_a_2270_);
lean_dec(v_a_2317_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_dec_ref_known(v___x_2329_, 1);
lean_dec_ref(v_name_2282_);
lean_dec_ref(v_cwd_2268_);
lean_dec_ref(v_env_2267_);
goto v___jp_2272_;
}
else
{
v___y_2303_ = v___x_2329_;
goto v___jp_2302_;
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
v___jp_2283_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2284_ = l_Lake_stringToLegalOrSimpleName(v_name_2282_);
lean_inc(v___x_2284_);
v___x_2285_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_2284_);
v___x_2286_ = l_Lake_joinRelative(v_cwd_2268_, v___x_2285_);
lean_inc_ref(v___x_2286_);
v___x_2287_ = l_IO_FS_createDirAll(v___x_2286_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; 
lean_dec_ref_known(v___x_2287_, 1);
v___x_2288_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(v_a_2270_, v___x_2286_, v___x_2284_, v_tmp_2265_, v_lang_2266_, v_env_2267_, v_offline_2269_);
return v___x_2288_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v___x_2286_);
lean_dec(v___x_2284_);
lean_dec_ref(v_env_2267_);
v_a_2289_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2291_ = v___x_2287_;
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2287_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2293_ = lean_io_error_to_string(v_a_2289_);
v___x_2294_ = 3;
v___x_2295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*1, v___x_2294_);
lean_inc_ref(v_a_2270_);
v___x_2296_ = lean_apply_2(v_a_2270_, v___x_2295_, lean_box(0));
v___x_2297_ = lean_box(0);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2297_);
v___x_2299_ = v___x_2291_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
v___jp_2302_:
{
if (lean_obj_tag(v___y_2303_) == 0)
{
lean_dec_ref_known(v___y_2303_, 1);
goto v___jp_2283_;
}
else
{
lean_dec_ref(v_name_2282_);
lean_dec_ref(v_cwd_2268_);
lean_dec_ref(v_env_2267_);
return v___y_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* v_name_2330_, lean_object* v_tmp_2331_, lean_object* v_lang_2332_, lean_object* v_env_2333_, lean_object* v_cwd_2334_, lean_object* v_offline_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
uint8_t v_tmp_boxed_2338_; uint8_t v_lang_boxed_2339_; uint8_t v_offline_boxed_2340_; lean_object* v_res_2341_; 
v_tmp_boxed_2338_ = lean_unbox(v_tmp_2331_);
v_lang_boxed_2339_ = lean_unbox(v_lang_2332_);
v_offline_boxed_2340_ = lean_unbox(v_offline_2335_);
v_res_2341_ = l_Lake_new(v_name_2330_, v_tmp_boxed_2338_, v_lang_boxed_2339_, v_env_2333_, v_cwd_2334_, v_offline_boxed_2340_, v_a_2336_);
lean_dec_ref(v_a_2336_);
return v_res_2341_;
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
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1);
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
